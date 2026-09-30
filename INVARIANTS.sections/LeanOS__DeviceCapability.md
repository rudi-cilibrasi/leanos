# Only the holder of a device permission can drive that device

Hardware drivers written as small Lean programs run inside the kernel, but only on behalf of a program that holds a *device permission* — a capability naming one approved device. The holder may attach a driver program to its device, but only one that passes the device's fence check, and may then run it a bounded number of steps at a time; the driver can pause to hand one event, such as a key press, back to its holder. These theorems guarantee that nobody else can make a device do anything, that running one device's driver never disturbs another device or anyone's permissions, that taking the permission away ends the holder's access, and that across any sequence of operations every device stays inside its fence.

- `cap_step_caps` — An ordinary permission operation changes the permission records exactly as the existing permission model says, so every guarantee already proved about permissions still applies.
- `non_cap_step_caps` — Granting, attaching, running and withdrawing device permissions never change the ordinary permission records.
- `device_state_changes_only_by_holder` — The only way a device's state ever changes is a run request from a program that currently holds that device's permission.
- `no_capability_no_effect` — A program without a device permission cannot attach or run a driver: its request is refused and nothing changes.
- `revoke_denies_invoke` — Once a device permission is withdrawn, the former holder's next run request is refused.
- `bind_accepted_admissible` — A driver is attached only if it carries the device's fence and passes the fence check for it.
- `step_inv` — Every single operation keeps two facts true: each attached driver passed its device's fence check, and no device has ever been asked to step outside its fence.
- `run_inv` — Those two facts stay true across any sequence of operations whatsoever.
- `initial_inv` — A freshly started system, with no permissions handed out and no drivers attached, satisfies both facts.
- `invoke_other_device_unchanged` — Running one device's driver leaves every other device untouched.
