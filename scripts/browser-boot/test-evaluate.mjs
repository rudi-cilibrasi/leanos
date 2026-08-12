// Offline unit tests for the browser harness decision logic and argument
// translation.  No browser or network is required.
import assert from 'node:assert/strict';
import { evaluate } from './evaluate.mjs';
import { parseArgs } from './qemu-wasm-shim.mjs';

let passed = 0;
function check(name, fn) {
  fn();
  passed += 1;
  console.log(`ok - ${name}`);
}

check('accepts a guest debug-exit with serial output', () => {
  const out = evaluate({ crossOriginIsolated: true, title: 'exit=33', serialBytes: 31359, timedOut: false });
  assert.equal(out.status, 'guest-exit');
  assert.equal(out.exitCode, 33);
});

check('passes a guest failure status through verbatim', () => {
  const out = evaluate({ crossOriginIsolated: true, title: 'exit=35', serialBytes: 400, timedOut: false });
  assert.equal(out.exitCode, 35);
});

check('rejects a debug-exit with no serial as a media failure', () => {
  const out = evaluate({ crossOriginIsolated: true, title: 'exit=33', serialBytes: 0, timedOut: false });
  assert.equal(out.status, 'no-serial-output');
  assert.notEqual(out.exitCode, 33);
});

check('reports missing cross-origin isolation', () => {
  const out = evaluate({ crossOriginIsolated: false, title: '', serialBytes: 0, timedOut: false });
  assert.equal(out.status, 'no-cross-origin-isolation');
  assert.notEqual(out.exitCode, 33);
});

check('reports a runtime abort', () => {
  const out = evaluate({ crossOriginIsolated: true, title: 'abort', serialBytes: 120, timedOut: false });
  assert.equal(out.status, 'runtime-abort');
  assert.notEqual(out.exitCode, 33);
});

check('maps a hung boot to the runner timeout status', () => {
  const out = evaluate({ crossOriginIsolated: true, title: 'running', serialBytes: 8000, timedOut: true });
  assert.equal(out.status, 'timeout');
  assert.equal(out.exitCode, 124);
});

check('rejects a run that never reached a guest exit', () => {
  const out = evaluate({ crossOriginIsolated: true, title: 'running', serialBytes: 200, timedOut: false });
  assert.equal(out.status, 'no-guest-exit');
  assert.notEqual(out.exitCode, 33);
});

check('translates the canonical argument vector for MEMFS', () => {
  const argv = [
    '-machine', 'q35,accel=tcg', '-nodefaults', '-cpu', 'max', '-smp', '1',
    '-m', '128M', '-display', 'none', '-monitor', 'none',
    '-serial', 'file:/home/x/build/boot/serial.log', '-no-reboot', '-no-shutdown', '-nic', 'none',
    '-device', 'intel-iommu,intremap=off,pt=off,caching-mode=off,device-iotlb=off,aw-bits=39,dma-translation=on,snoop-control=off',
    '-device', 'VGA,bus=pcie.0,addr=0x1',
    '-device', 'isa-debug-exit,iobase=0xf4,iosize=0x04',
    '-drive', 'id=leanos-cd,if=none,format=raw,media=cdrom,readonly=on,file=/home/x/build/boot/leanos-0.1.0-x86_64.iso',
    '-device', 'ide-cd,drive=leanos-cd,bus=ide.0',
  ];
  const parsed = parseArgs(argv);
  assert.equal(parsed.serialFile, '/home/x/build/boot/serial.log');
  assert.equal(parsed.image, '/home/x/build/boot/leanos-0.1.0-x86_64.iso');
  assert.equal(parsed.memory, '128M');
  // Host paths are redirected to fixed MEMFS paths; the pinned intel-iommu and
  // debug-exit device survive verbatim; the firmware search path is ensured.
  assert.ok(parsed.browserArgs.includes('file:/serial.log'));
  assert.ok(parsed.browserArgs.some((a) => a.includes('file=/leanos.iso')));
  assert.ok(parsed.browserArgs.some((a) => a.startsWith('intel-iommu,')));
  assert.ok(parsed.browserArgs.includes('isa-debug-exit,iobase=0xf4,iosize=0x04'));
  const dashL = parsed.browserArgs.indexOf('-L');
  assert.ok(dashL >= 0 && parsed.browserArgs[dashL + 1] === '/pack-rom/');
  // No host absolute path leaks into the guest argument vector.
  assert.ok(!parsed.browserArgs.some((a) => a.includes('/home/x/')));
});

check('preserves an existing firmware search path without duplicating it', () => {
  const parsed = parseArgs(['-L', '/custom-rom/', '-serial', 'file:/tmp/s.log', '-drive', 'file=/tmp/a.iso']);
  assert.equal(parsed.browserArgs.filter((a) => a === '-L').length, 1);
  assert.ok(parsed.browserArgs.includes('/custom-rom/'));
});

console.log(`\n${passed} browser-harness unit checks passed`);
