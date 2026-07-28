if (typeof Module === 'undefined') {
  Module = {};
}

Module.arguments = [
  '-nographic',
  '-machine', 'q35',
  '-cpu', 'max',
  '-smp', '1',
  '-m', '128M',
  '-accel', 'tcg,tb-size=500',
  '-L', '/pack-rom/',
  '-monitor', 'none',
  '-nic', 'none',
  '-no-reboot',
  '-no-shutdown',
  '-device', 'isa-debug-exit,iobase=0xf4,iosize=0x04',
  '-cdrom', '/leanos.iso',
  '-boot', 'c',
];

Module.locateFile = (path) => `./${path}`;
Module.mainScriptUrlOrBlob = `${location.origin}${location.pathname.replace(/[^/]*$/, '')}out.js`;
