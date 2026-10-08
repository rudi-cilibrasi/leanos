# Keyboard echo: the keyboard permission is not the console permission

These theorems describe the `keyboard-echo` boot image, which joins the keyboard driver service and the console server. One program holds the *device permission* for the keyboard: it receives each key the driver produces and sends it to the console server. The console server holds the *console permission* and prints each key. A third program holds nothing. The theorems put the earlier keyboard-permission model and the console model side by side, without changing either, and show that the two permissions stay with different programs: only the console-permission holder makes the console print, and only the device-permission holder makes the keyboard do anything. The kernel's table of who holds the keyboard is checked against the console model when the image boots, but it is not derived from these theorems, and no theorem here says the booted code follows the model step by step.

- `device_holder_not_console` — In the permission layout the image installs, the program holding the keyboard permission does not hold the console permission.
- `console_holder_no_device` — In that layout, the program holding the console permission holds no keyboard permission.
- `device_holder_write_refused` — When the keyboard program tries to print on the console directly, it is refused and nothing changes.
- `step_output_of_not_console` — An action of a program without the console permission never changes what the console shows; a message it sends only waits at the server.
- `run_output_without_console` — A whole run in which no console-permission holder acts leaves what the console shows unchanged.
- `composed_console_only_by_holder` — In the combined system of console and devices, a step that changes what the console shows is always an action of a console-permission holder.
- `composed_device_only_by_holder` — In the combined system, a step that changes a device's state is always a run of the device's program by a holder of that device's permission.
- `boot_causes_distinct` — With the permissions the image installs, only the console server can make the console print, and only the keyboard program can make the keyboard device do anything.
- `server_no_device_effects` — The console server is never given the keyboard permission, so every attempt it makes to load or run a keyboard program is refused and leaves every device exactly as it was.
- `boot_output` — In the run that the keyboard-echo boot image performs, the console shows exactly the typed keys: `lean ipc` and a newline.
- `boot_b_refused` — In that run, the program without permissions has all three of its attempts refused.
- `boot_a_observations` — In that run, the keyboard program's attempt to print directly is refused, and each key it sends to the server is accepted.
