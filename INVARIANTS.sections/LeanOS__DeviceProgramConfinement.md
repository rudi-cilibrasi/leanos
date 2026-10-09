# Keeping hardware drivers inside their fence

LeanOS drives its WiFi card and USB keyboard controller with small programs written in Lean and run by a tiny interpreter. Each program gets a written fence — a policy naming the stretch of device registers it may touch, the few configuration settings it may read or change, which switches of the device's master control register it may flip, and whether it may learn physical memory addresses for the device to copy data to on its own. These theorems guarantee that a program which passes the automatic fence check, or whose image carries its fence for the interpreter to enforce, never asks the hardware for anything outside that fence — whatever the device answers and however long the program runs. A fence may also carry a map of the places in the program's scratch memory where the device expects to find memory addresses; the theorems guarantee that every such place only ever holds zero or an address inside the program's own scratch area. They are proved about the interpreter's reference model; that the real interpreter matches the model is tested, not proved.

- `iter_preserve` — A stepping-stone fact: if each round of a repeated operation keeps a property true, the whole repetition keeps it true.
- `mmioOk_mono` — A stepping-stone fact: a register access that fits in a smaller window also fits in any larger window.
- `setReg_dev` — Bookkeeping: changing one of the interpreter's scratch registers leaves the device's state alone.
- `setReg_stack` — Bookkeeping: changing a scratch register leaves the interpreter's return stack alone.
- `setReg_mem` — Bookkeeping: changing a scratch register leaves the program's scratch memory alone.
- `Step.machine_next` — Bookkeeping: the state left by an instruction that continues is exactly the state it produced.
- `Step.machine_stop` — Bookkeeping: the state left by an instruction that stops is exactly the state it stopped in.
- `Step.machine_ite` — Bookkeeping: looking at the state an either-or instruction leaves is the same as looking inside whichever branch was taken.
- `exec_confined` — Any single instruction that passed the fence check, executed from a clean state, requests no hardware action outside the fence.
- `exec_declared_confined` — Any single instruction at all, in a program whose image carries its fence, requests no hardware action outside that fence: the interpreter's own checks stop it first.
- `loop_flag` — A stepping-stone fact: if every single step keeps the "stepped outside the fence" alarm off, then a whole run of any length keeps it off.
- `run_confined` — A program accepted by the fence check never asks the hardware for anything outside its fence — no register outside its window, no forbidden configuration setting, no forbidden control switch, no memory address unless allowed, and never a memory address outside its own scratch area in the registers where the device looks up its data structures — on any device, from any starting registers and memory, for any number of steps.
- `run_declared_confined` — Any program whose image carries a fence, even one the checker never saw, is held inside that fence by the interpreter's run-time checks alone.
- `exec_descOk` — Any single instruction of a program whose image carries its fence keeps every address slot named in the fence's memory map holding zero or an address inside the program's own scratch area.
- `loop_descOk` — A stepping-stone fact: if the address slots are all in order before a run, they are still in order after a run of any length.
- `get_zero` — A stepping-stone fact: every byte of freshly zeroed memory reads as zero.
- `le32_zero` — A stepping-stone fact: every four-byte value read from the interpreter's freshly zeroed scratch memory is zero.
- `descOk_zero` — Freshly zeroed scratch memory, as every program starts with, satisfies any fence's address-slot map.
- `run_declared_descriptors` — A program whose image carries its fence, run from zeroed scratch for any number of steps, never leaves an address the device will follow pointing outside the program's own scratch area — provided the scratch area's physical address stays fixed.
- `run_admissible_descriptors` — The same holds for every program the fence check accepts: a fence with an address-slot map is only accepted when the program's image carries it.
- `step_stack_bounded` — The interpreter's record of pending subroutine returns never grows past its fixed limit of 16.
- `sane_cfgWrite_outside_header` — Under a sensible fence, a program may never directly overwrite the device's identity, master control switches, or the address ranges it answers to.
- `sane_update_bus_master` — Under a sensible fence, a program can switch on the device's ability to read and write main memory on its own only if the fence explicitly allows that, and can never switch on the old port-based access mode.
- `qotomAhciPolicy_sane` — The disk controller's fence on the lab machine is a sensible fence.
- `qotomAhciPolicy_bits` — The disk controller fence's configuration settings are exactly the ones the lab kernel's own table lists, bit for bit.
- `qotomRtl8168Policy_sane` — The wired network card's fence on the lab machine is a sensible fence.
- `qotomRtl8168Policy_bits` — The wired network card fence's configuration settings are exactly the ones the lab kernel's own table lists, bit for bit.
- `q35XhciPolicy_sane` — The fence for the emulated USB controller used in the QEMU test lab is a sensible fence.
- `xhciPolicies_descWf` — The address-slot maps of both USB controller fences, on the lab machine and in the QEMU test lab, are ones the real interpreter accepts: few enough regions, each inside the scratch area.
- `qotomBcm43224Policy_sane` — The WiFi card's fence on the lab machine is a sensible fence.
- `qotomXhciPolicy_sane` — The USB controller's fence on the lab machine is a sensible fence.
- `qotomBcm43224Policy_no_bus_master` — The WiFi driver can never switch on the card's ability to reach main memory by itself; it moves every frame through the card's registers instead.
- `qotomBcm43224Policy_bits` — The WiFi fence's configuration settings are exactly the ones the lab kernel's own table lists, bit for bit.
- `qotomXhciPolicy_bits` — The USB controller fence's configuration settings are exactly the ones the lab kernel's own table lists, bit for bit.
