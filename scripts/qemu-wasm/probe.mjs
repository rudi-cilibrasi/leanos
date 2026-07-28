import fs from 'node:fs';
import puppeteer from 'puppeteer-core';

const output = process.argv[2];
if (!output) throw new Error('usage: node probe.mjs OUTPUT.json');
const timeout = Number(process.env.LEANOS_QEMU_WASM_TIMEOUT_MS || '180000');
const consoleMessages = [];
const pageErrors = [];
let waitError = null;
let browser;
let page;

try {
  browser = await puppeteer.launch({
    executablePath: '/usr/bin/google-chrome',
    headless: true,
    args: ['--no-sandbox', '--disable-gpu'],
  });
  page = await browser.newPage();
  page.on('console', (message) => consoleMessages.push(message.text()));
  page.on('pageerror', (error) => pageErrors.push(error.stack || String(error)));
  await page.goto('http://127.0.0.1:8765/', { waitUntil: 'networkidle0' });
  try {
    await page.waitForFunction(
      () => document.title.startsWith('exit=') || document.title === 'abort',
      { timeout },
    );
  } catch (error) {
    waitError = error.message;
  }
} catch (error) {
  waitError = error.stack || String(error);
}

let pageResult = {};
if (page) {
  try {
    pageResult = await page.evaluate(() => {
      const lines = [];
      const buffer = window.testXterm?.buffer.active;
      if (buffer) {
        for (let i = 0; i < buffer.length; i += 1) {
          const line = buffer.getLine(i);
          if (!line) continue;
          const text = line.translateToString(true);
          if (line.isWrapped && lines.length > 0) lines[lines.length - 1] += text;
          else if (text) lines.push(text);
        }
      }
      return {
        title: document.title,
        status: document.getElementById('status')?.textContent || '',
        transcript: lines.join('\n'),
        probe: window.leanosProbe || {},
      };
    });
  } catch (error) {
    pageErrors.push(error.stack || String(error));
  }
}

fs.writeFileSync(output, `${JSON.stringify({
  ...pageResult,
  console: consoleMessages,
  pageErrors,
  waitError,
}, null, 2)}\n`);
if (browser) await browser.close();
