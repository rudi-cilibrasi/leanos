# Platform admission profiles

`LeanOS.PlatformAdmission` provides the closed whole-platform gate used before
CPL3. The two accepted profile IDs and their machine-readable manifests are:

| Profile | Code/version | Isolation | Optional facilities | Terminal |
| --- | --- | --- | --- | --- |
| `q35-v1` | `1/1` | WP, SMEP, SMAP, VT-d | assigned EDU supported | serial `FINAL`, absorbing halt, optional QEMU debug exit |
| `qotom-j1900-clbtm210-v2` | `2/2` | WP, NXE, SMEP, closed/copy roots | VT-d and assigned EDU not applicable | serial `FINAL`, absorbing `cli; hlt`, watchdog recovery |

The component words are identities, not independent capabilities. Each is
accepted only with the complete manifest selected by the profile code and
version. The generated boundary returns:

| Word | Meaning |
| --- | --- |
| 0 | ABI version (`1`) |
| 1 | complete profile accepted |
| 2 | stable rejection reason (`0` on success) |
| 3 | selected profile code |
| 4 | bounded CPL3 authority |
| 5 | semantic serial-final-and-halt policy |
| 6 | q35 debug-exit convenience |
| 7 | AP-start publication (always zero) |

Rejection reasons are unknown profile, wrong version, firmware root, memory
map, PCI, UART, BSP, forbidden AP start, isolation, facility policy, scenario,
and terminal, numbered 1 through 12. The hosted harness changes every input,
including direct q35/Qotom component splices, and requires the exact reason.

The Qotom component manifest is seeded by the earlier accepted physical
blocking-IPC capture and closed by the
[profile-bound 2026-09-13 capture](../hardware/lab/observations/qotom-platform-admission-20260913/README.md).
That final capture contains this line immediately before `QOTOM-IPC-READY`:

```text
LEANOS-LAB/1 PLATFORM-ADMISSION profile=qotom-j1900-clbtm210-v2 version=2 status=PASS cpl3-authority=1 vtd=not-applicable assigned-edu=not-applicable terminal=serial-final-halt
```

The q35 call is deliberately silent on success so the existing versioned
serial protocol remains unchanged. Any profile disagreement uses the existing
fatal terminal path before user entry.

The accepted ELF has SHA256
`2ca33caa063698c1648fbc630c27d8c9ccc46031553ef479de881b792b51e9e5`;
the full serial stream has SHA256
`45acf984db238993b6e6b085312f70b21e78a7a7c80b44dc2d8a2727d1a2c4c4`.
The watchdog restored FreeBSD and the one-shot request was consumed.

Validate the model, generated boundary, registry, and release consumers with:

```sh
lake build LeanOS.PlatformAdmission LeanOS.SecurityClaims
LEANOS_HOSTED_BOUNDARY_ID=platform-admission \
  scripts/check-boot-handoff-host.sh ordinary
python3 scripts/check-platform-profiles.py --self-test
python3 scripts/test-release-artifact-consumers.py
```

[ADR 0019](adr/0019-typed-platform-admission.md) records the decision and
residual trust boundary.
