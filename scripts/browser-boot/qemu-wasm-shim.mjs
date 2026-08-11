#!/usr/bin/env node
// QEMU-shaped shim for the LeanOS qemu-wasm browser compatibility harness.
//
// `scripts/run-image.sh` invokes this exactly like the native emulator: it
// answers `--version`, accepts the canonical `leanos_q35_command` argument
// vector, boots those bytes in a pinned browser WebAssembly QEMU, writes the
// guest serial to the requested `-serial file:` target, and exits with the
// guest debug-exit status.  The runner then performs its unchanged canonical
// protocol, DMA-snapshot, and VT-d activation validation on the captured
// serial, so the browser path reuses every native acceptance check instead of
// a browser-only shortcut.
//
// The only guest-visible transformation of the argument vector is redirecting
// the host serial-log and ISO paths to fixed MEMFS paths and ensuring the
// firmware search path (`-L /pack-rom/`) the WebAssembly build needs is
// present.  The machine, CPU, memory, device topology (including the pinned
// intel-iommu), and debug-exit device pass through verbatim.

import fs from 'node:fs';
import http from 'node:http';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(HERE, '..', '..');
const RUNTIME_DIR = process.env.LEANOS_BROWSER_RUNTIME
  || path.join(REPO, 'build', 'browser', 'runtime');
const VERSION_LINE = 'LeanOS qemu-wasm browser shim (qemu-wasm 8.2.0 prebuilt, ktock/qemu-wasm-demo 0208c86)';
const MEMFS_SERIAL = '/serial.log';
const MEMFS_ISO = '/leanos.iso';

export function parseArgs(argv) {
  const result = { serialFile: null, image: null, memory: '128M', browserArgs: [] };
  let sawFirmwarePath = false;
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = argv[i + 1];
    if (arg === '-serial' && typeof next === 'string' && next.startsWith('file:')) {
      result.serialFile = next.slice('file:'.length);
      result.browserArgs.push('-serial', `file:${MEMFS_SERIAL}`);
      i += 1;
      continue;
    }
    if (arg === '-m' && typeof next === 'string') {
      result.memory = next;
      result.browserArgs.push('-m', next);
      i += 1;
      continue;
    }
    if (arg === '-L') {
      sawFirmwarePath = true;
      result.browserArgs.push('-L', next);
      i += 1;
      continue;
    }
    if (arg === '-drive' && typeof next === 'string' && /(^|,)file=/.test(next)) {
      const file = /(?:^|,)file=([^,]+)/.exec(next);
      if (file) result.image = file[1];
      result.browserArgs.push('-drive', next.replace(/((?:^|,)file=)[^,]+/, `$1${MEMFS_ISO}`));
      i += 1;
      continue;
    }
    result.browserArgs.push(arg);
  }
  if (!sawFirmwarePath) result.browserArgs.push('-L', '/pack-rom/');
  return result;
}

function moduleSource(browserArgs) {
  return `if (typeof Module === 'undefined') { Module = {}; }
Module.arguments = ${JSON.stringify(browserArgs)};
Module.locateFile = (path) => './' + path;
Module.mainScriptUrlOrBlob = location.origin + location.pathname.replace(/[^/]*$/, '') + 'out.js';
Module.preRun = Module.preRun || [];
Module.preRun.push(() => {
  Module.addRunDependency('leanos-iso');
  fetch('./leanos.iso').then((r) => r.arrayBuffer()).then((buf) => {
    Module.FS.writeFile(${JSON.stringify(MEMFS_ISO)}, new Uint8Array(buf));
    Module.removeRunDependency('leanos-iso');
  });
});
`;
}

const MIME = {
  '.html': 'text/html; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.mjs': 'text/javascript; charset=utf-8',
  '.wasm': 'application/wasm',
  '.data': 'application/octet-stream',
  '.iso': 'application/octet-stream',
  '.json': 'application/json',
};

function startServer(rootDir) {
  const server = http.createServer((request, response) => {
    const requested = decodeURIComponent(request.url.split('?')[0]);
    const relative = requested === '/' ? '/index.html' : requested;
    const filePath = path.join(rootDir, path.normalize(relative));
    if (!filePath.startsWith(rootDir)) {
      response.writeHead(403).end();
      return;
    }
    fs.readFile(filePath, (error, data) => {
      if (error) {
        response.writeHead(404).end();
        return;
      }
      response.writeHead(200, {
        'Content-Type': MIME[path.extname(filePath)] || 'application/octet-stream',
        // Same isolation headers the deployed service worker injects, so the
        // first load is already cross-origin isolated under automation.
        'Cross-Origin-Opener-Policy': 'same-origin',
        'Cross-Origin-Embedder-Policy': 'require-corp',
      });
      response.end(data);
    });
  });
  return new Promise((resolve) => {
    server.listen(0, '127.0.0.1', () => resolve(server));
  });
}

// Launch the pinned browser, wait for a guest debug-exit / abort / timeout,
// and return the captured runtime observation plus the MEMFS serial bytes.
async function runInBrowser(stagingDir, { timeoutMs, browserPath }) {
  const puppeteer = (await import('puppeteer-core')).default;
  const server = await startServer(stagingDir);
  const port = server.address().port;
  const consoleErrors = [];
  const browser = await puppeteer.launch({
    executablePath: browserPath,
    headless: true,
    args: ['--no-sandbox', '--disable-gpu'],
  });
  try {
    const page = await browser.newPage();
    page.on('pageerror', (error) => consoleErrors.push(error.message));
    await page.goto(`http://127.0.0.1:${port}/`, { waitUntil: 'networkidle0' });
    await page.waitForFunction(() => window.leanosCrossOriginIsolated !== undefined, {
      timeout: 20000,
    });
    let timedOut = false;
    try {
      await page.waitForFunction(
        () => document.title.startsWith('exit=') || document.title === 'abort',
        { timeout: timeoutMs, polling: 200 },
      );
    } catch {
      timedOut = true;
    }
    const observed = await page.evaluate(() => {
      let serial = '';
      try {
        serial = window.qemuModule.FS.readFile('/serial.log', { encoding: 'binary' });
      } catch {
        serial = '';
      }
      return {
        crossOriginIsolated: Boolean(window.leanosCrossOriginIsolated),
        title: document.title,
        serial: Array.from(serial),
      };
    });
    const serialBuffer = Buffer.from(observed.serial);
    return {
      crossOriginIsolated: observed.crossOriginIsolated,
      title: observed.title,
      serialBytes: serialBuffer.length,
      timedOut,
      consoleErrors,
      serialBuffer,
    };
  } finally {
    await browser.close();
    server.close();
  }
}

async function main(argv) {
  if (argv.includes('--version')) {
    process.stdout.write(`${VERSION_LINE}\n`);
    return 0;
  }
  const { evaluate } = await import('./evaluate.mjs');
  const parsed = parseArgs(argv);
  if (!parsed.serialFile || !parsed.image) {
    process.stderr.write('browser-shim: missing -serial file: or -drive file= argument\n');
    return 64;
  }
  if (!fs.existsSync(RUNTIME_DIR)) {
    process.stderr.write(
      `browser-shim: runtime not staged at ${RUNTIME_DIR}; run scripts/prepare-browser-runtime.sh\n`,
    );
    return 64;
  }
  const browserPath = process.env.LEANOS_BROWSER;
  if (!browserPath || !fs.existsSync(browserPath)) {
    process.stderr.write('browser-shim: set LEANOS_BROWSER to the pinned Chrome-for-Testing binary\n');
    return 64;
  }
  const timeoutMs = Number(process.env.LEANOS_BROWSER_TIMEOUT_MS || 220000);

  const staging = fs.mkdtempSync(path.join(os.tmpdir(), 'leanos-browser-'));
  try {
    for (const name of [
      'coi-serviceworker.js', 'out.js', 'qemu-system-x86_64.wasm',
      'qemu-system-x86_64.worker.js', 'load-rom.js', 'load-rom.data', 'xterm-pty.js',
    ]) {
      fs.copyFileSync(path.join(RUNTIME_DIR, name), path.join(staging, name));
    }
    fs.copyFileSync(path.join(HERE, 'page.html'), path.join(staging, 'index.html'));
    fs.writeFileSync(path.join(staging, 'module.js'), moduleSource(parsed.browserArgs));
    fs.copyFileSync(parsed.image, path.join(staging, 'leanos.iso'));

    const captured = await runInBrowser(staging, { timeoutMs, browserPath });
    // Write whatever serial the guest produced so run-image.sh validates the
    // real transcript; an empty file still fails the canonical protocol gate.
    fs.mkdirSync(path.dirname(parsed.serialFile), { recursive: true });
    fs.writeFileSync(parsed.serialFile, captured.serialBuffer);

    const outcome = evaluate(captured);
    if (outcome.status !== 'guest-exit') {
      process.stderr.write(
        `browser-shim: runtime outcome ${outcome.status}`
        + (captured.consoleErrors.length ? ` (${captured.consoleErrors[0]})` : '')
        + `; serial-bytes=${captured.serialBytes}\n`,
      );
    }
    return outcome.exitCode;
  } finally {
    fs.rmSync(staging, { recursive: true, force: true });
  }
}

const invokedDirectly = process.argv[1]
  && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url);
if (invokedDirectly) {
  main(process.argv.slice(2)).then(
    (code) => process.exit(code),
    (error) => {
      process.stderr.write(`browser-shim: ${error && error.stack ? error.stack : error}\n`);
      process.exit(70);
    },
  );
}
