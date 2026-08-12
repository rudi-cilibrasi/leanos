// Fixed canonical q35 construction for the public LeanOS browser demo.
// This mirrors scripts/q35-platform.sh (the pinned intel-iommu unit, one vCPU,
// no network, explicit VGA / debug-exit devices) so the browser runs the same
// reviewed machine as the native emulator.
//
// Serial is written to an in-memory file rather than a pseudo-terminal.  With
// no stdio character device, QEMU's main loop never enters Emscripten's
// blocking TTY poll (which would otherwise starve the timers and block-I/O
// completions and stop the guest from reading its boot media); the page tails
// the file into the terminal for display instead.  The guest ends with the
// isa-debug-exit status the native harness validates.
if (typeof Module === 'undefined') { Module = {}; }

Module.arguments = [
  '-machine', 'q35,accel=tcg',
  '-nodefaults',
  '-cpu', 'max',
  '-smp', '1',
  '-m', '128M',
  '-display', 'none',
  '-monitor', 'none',
  '-serial', 'file:/serial.log',
  '-no-reboot',
  '-no-shutdown',
  '-nic', 'none',
  '-L', '/pack-rom/',
  '-device', 'intel-iommu,intremap=off,pt=off,caching-mode=off,device-iotlb=off,aw-bits=39,dma-translation=on,snoop-control=off',
  '-device', 'VGA,bus=pcie.0,addr=0x1',
  '-device', 'isa-debug-exit,iobase=0xf4,iosize=0x04',
  '-drive', 'id=leanos-cd,if=none,format=raw,media=cdrom,readonly=on,file=/leanos.iso',
  '-device', 'ide-cd,drive=leanos-cd,bus=ide.0',
];

Module.locateFile = (path) => `./${path}`;
Module.mainScriptUrlOrBlob = `${location.origin}${location.pathname.replace(/[^/]*$/, '')}out.js`;

// Inject the canonical ISO into the Emscripten filesystem without touching the
// upstream firmware preload: register a run dependency, fetch the bytes, write
// them to /leanos.iso, then release so QEMU starts with the disk present.
Module.preRun = Module.preRun || [];
Module.preRun.push(() => {
  Module.addRunDependency('leanos-iso');
  fetch('./leanos.iso')
    .then((response) => response.arrayBuffer())
    .then((buffer) => {
      Module.FS.writeFile('/leanos.iso', new Uint8Array(buffer));
      Module.removeRunDependency('leanos-iso');
    });
});
