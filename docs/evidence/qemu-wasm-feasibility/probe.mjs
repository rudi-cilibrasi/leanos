import puppeteer from 'puppeteer-core';

const browser = await puppeteer.launch({
  executablePath: '/usr/bin/google-chrome',
  headless: true,
  args: ['--no-sandbox', '--disable-gpu'],
});
const page = await browser.newPage();
page.on('console', (message) => console.log(`console: ${message.text()}`));
page.on('pageerror', (error) => console.log(`pageerror: ${error.stack}`));
await page.goto('http://127.0.0.1:8765/', { waitUntil: 'networkidle0' });
await page.waitForFunction(() => crossOriginIsolated, { timeout: 15000 });
try {
  await page.waitForFunction(
    () => document.title === 'exit=33' || document.title === 'abort',
    { timeout: 180000 },
  );
} catch (error) {
  console.log(`wait: ${error.message}`);
}
const result = await page.evaluate(() => {
  const buffer = window.testXterm.buffer.active;
  const lines = [];
  for (let i = 0; i < buffer.length; i += 1) {
    const line = buffer.getLine(i)?.translateToString(true);
    if (line) lines.push(line);
  }
  return {
    title: document.title,
    status: document.getElementById('status').textContent,
    transcript: lines.join('\n'),
  };
});
console.log(JSON.stringify(result, null, 2));
await browser.close();
