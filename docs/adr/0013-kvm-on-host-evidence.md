# ADR 0013: Non-blocking KVM-on-host evidence

## Status

Accepted as an experimental evidence lane.

## Decision

Run the existing four-shard pull-request emulator matrix in an additional
GitHub Actions job when an explicit KVM preflight succeeds. The job runs on an
Ubuntu 24.04 host runner and passes `/dev/kvm` into the pinned LeanOS CI image.
It retains the reviewed `q35` machine, `-nodefaults`, `-cpu max` feature model,
one-vCPU default, memory, device inventory, guest images, scenario timeouts,
serial protocol, and result classifications. Because KVM otherwise inherits
the physical host's CPUID vendor, the KVM construction explicitly adds
`vendor=AuthenticAMD`. It also requires `pku=on,enforce=on`, because the
existing peer-PKE negative relies on the `max` CPU's PKU feature. This preserves
the existing guest-visible CPU contract on both Intel and AMD hosted runners;
a host unable to realize it is classified as unavailable by preflight.

The runner selects exactly one accelerator through
`LEANOS_QEMU_ACCELERATOR`: `tcg` for the required emulator lane or `kvm` for
this experimental lane. Accelerator fallback lists are invalid. Before any
guest build or boot, `scripts/probe-kvm.py` checks that `/dev/kvm` is a
read-write character device, that QEMU lists KVM, and that a minimal
`q35,accel=kvm` process reports `kvm support: enabled`. A missing device,
permission failure, device-mapping failure, unsupported accelerator, failed
initialization, unavailable fixed guest CPU contract, or unconfirmed effective
accelerator produces a distinct machine-readable `unavailable` result. It is
not a passing KVM observation.

The initial job is bounded by the same four-way PR-tier sharding and a 60-minute
job timeout, publishes its preflight and available scenario evidence for 14
days, and is non-blocking. Runner-side KVM availability is an external service
capability, so an outage remains visible without preventing an otherwise valid
change from merging.

## CPU and platform policy

The guest CPU contract remains QEMU's `max` virtual CPU rather than `host`, with
the existing `AuthenticAMD` vendor fixed explicitly as
`max,vendor=AuthenticAMD,pku=on,enforce=on` under KVM. This prevents
Intel-versus-AMD runner placement from silently changing the guest-visible
vendor and prevents a missing PKU feature from becoming a misleading peer-PKE
semantic failure. The physical CPU model, kernel, architecture, runner image,
QEMU version, accelerator list, source revision, and run identity are recorded
as execution context. Variation in those host facts is accepted for this
observation lane only when the fixed guest CPU can be realized; it does not
broaden the admitted q35 guest platform. Other host-bounded feature differences
remain observable and must not be masked or treated as passing evidence.

## Evidence and trust boundary

The three evidence classes are deliberately separate:

| Class | What it observes | Additional trusted execution substrate | Excluded claim |
| --- | --- | --- | --- |
| Required q35/TCG | Deterministic integration behavior in QEMU software emulation | QEMU/TCG and the hosted build environment | Host-silicon or physical-machine behavior |
| Experimental q35/KVM | The same guest scenarios while eligible instructions execute through hardware virtualization | Host CPU, host kernel and KVM, runner virtualization, QEMU's KVM and device models | Bare-metal firmware, SMM, physical UART, or hardware VT-d behavior |
| Future bare metal | A separately admitted physical platform and real peripherals | Platform firmware, physical CPU, chipset, and laboratory automation | Any claim not defined by that future platform contract |

KVM evidence can expose differences between TCG and hardware-assisted execution,
but it remains integration evidence. It does not prove binary refinement,
kernel correctness, equivalence between TCG and KVM, or correctness on bare
metal. QEMU still supplies the q35 chipset and configured devices, and the
hosted runner may itself be virtualized.

## Promotion policy

Making this lane required needs a separate policy pull request. That change may
be proposed only after all of the following are documented from default-branch
or merge-queue runs:

- at least 50 complete four-shard KVM-available runs over at least 30 days;
- the latest 20 complete available runs are consecutively green;
- fewer than 2 percent of available shard executions need an infrastructure
  rerun, with no semantic classification mismatch;
- no observed TCG fallback, unclassified probe result, or incomplete evidence
  bundle; and
- an assigned response owner and a written policy for hosted-runner KVM outages,
  including when the required check may be disabled and how it is restored.

Unavailable runs do not count toward the green-run thresholds. A runner-service
change that prevents collecting enough available runs blocks promotion rather
than weakening the preflight or accepting fallback.

## Consequences

The repository gets earlier evidence about hardware-virtualized x86 behavior
without changing the required TCG gate or claiming real-hardware coverage. The
cost is an additional PR-tier build and emulator run for each available shard,
plus reliance on a hosted capability that is intentionally not yet a merge
requirement.
