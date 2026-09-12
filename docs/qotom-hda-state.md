# Qotom HDA ring and stream observation

The accepted native global capture advertises GCAP `4401` with GCTL `1` before
and after, version 1.0 and INTCTL zero. The next reader binds that exact profile
and observes the state needed to choose a shutdown policy for issue #330.

[Intel 329670-002](https://cdn.centralpoint.be/objects/pdf/9/96e/1597181_1_processoren-intel-celeron-processor-g1620t-2m-cache-240-ghz-cm8063701448300.pdf),
sections 15.6.20/27/33 and table 123, defines CORBCTL and RIRBCTL as bytes at
`4c`/`5c`, DPLBASE as a DWORD at `70`, and eight combined stream control/status
DWORDs at `80,a0,c0,e0,100,120,140,160` (hexadecimal). CORB/RIRB bit 1 and stream
bit 1 report DMA run state. DPLBASE bit 0 enables position-buffer updates.
These are raw sequential observations; clear bits alone do not prove fabric
drain or continuing firmware/AP exclusion. The reader neither follows the
position-buffer pointer nor acknowledges stream status.

The helper performs a complete 18-read global/resource refresh, requires the
accepted profile, reads eleven state registers with their exact widths, then
repeats the full 18-read refresh. Success takes exactly 47 reads. Any failed
read, changed profile/resource, narrow value with excess bits or all-ones sample
rejects with zero output. Initial/final global checks include GCTL.CRST. The
profile gate prevents choosing eight stream addresses under a different GCAP.

Tests cover every read-failure position, all prior/global/payload bits, narrow
width bounds, all-ones values, PCI drift in all four configuration-check phases,
all offsets and widths, malformed headers and missing inputs. Successful raw
samples can describe running engines; no shutdown inference is made here.
No write, polling or reset callback exists. Native emission and physical capture remain pending, followed by the actual shutdown/BME policy.

## Mapping authority

The state window permits only the eleven address/width pairs and maps page
`d0910000` as read-only/NX/supervisor UC. It keeps the sampled value private until
the original leaf is restored, both invalidations complete and final controls
match. Mapping/control interference terminates after cleanup; failed loads do
not publish values. Other HDA registers remain outside this window.

Arming requires a successful exact global profile, then privately reuses the
firmware/root/resource checks of the global reader. It excludes all 4096
low-memory aliases to all four pages of the 16 KiB HDA resource. Every rejected
rearm clears prior authority without device access. Window and arm tests cover
all accepted widths, invalid offsets/widths, aliases, missing callbacks, invalid
apertures, mapping/control interference and every bit of the prior profile.
