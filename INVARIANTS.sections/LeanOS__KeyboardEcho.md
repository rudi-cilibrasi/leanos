# Keyboard echo: the keyboard permission is not the console permission

These theorems describe the `keyboard-echo` boot image, which joins the keyboard driver service and the console server. One program holds the *device permission* for the keyboard: it receives each key the driver produces and sends it to the console server. The console server holds the *console permission* and prints each key. A third program holds nothing. The theorems put the earlier keyboard-permission model and the console model side by side, without changing either, and show that the two permissions stay with different programs: only the console-permission holder makes the console print, and only the device-permission holder makes the keyboard do anything. The kernel's table of who holds the keyboard is checked, when the image boots and on every keyboard request, against a small generated checker that these theorems tie to the keyboard-permission model; the table is not derived from the theorems, and no theorem here says the booted code follows the model step by step.

- `device_holder_not_console` — In the permission layout the image installs, the program holding the keyboard permission does not hold the console permission.
- `console_holder_no_device` — In that layout, the program holding the console permission holds no keyboard permission.
- `device_holder_write_refused` — When the keyboard program tries to print on the console directly, it is refused and nothing changes.
- `step_output_of_not_console` — An action of a program without the console permission never changes what the console shows; a message it sends only waits at the server.
- `run_output_without_console` — A whole run in which no console-permission holder acts leaves what the console shows unchanged.
- `composed_console_only_by_holder` — In the combined system of console and devices, a step that changes what the console shows is always an action of a console-permission holder.
- `composed_device_only_by_holder` — In the combined system, a step that changes a device's state is always a run of the device's program by a holder of that device's permission.
- `boot_causes_distinct` — With the permissions the image installs, only the console server can make the console print, and only the keyboard program can make the keyboard device do anything.
- `server_no_device_effects` — The console server is never given the keyboard permission, so every attempt it makes to load or run a keyboard program is refused and leaves every device exactly as it was.
- `boot_grant_installs` — Starting from no keyboard permissions, the kernel's one act of giving the keyboard to the keyboard program produces exactly the permission layout the image uses.
- `deviceAuthorize_agrees` — The small number-in, number-out checker built into the kernel answers "yes" for a program and a device exactly when that program holds that device's permission in the installed layout, and "no" otherwise.
- `deviceAuthorize_off_domain` — For a program number the image does not use, the checker gives neither answer.
- `deviceAuthorize_accepts` — The checker says "yes" only to the keyboard program, and only for the keyboard.
- `witnesses_disjoint` — The keyboard checker and the console checker never favour the same program: whoever the keyboard checker accepts is refused console printing and reading, and whoever may print or read the console is refused every device.
- `deviceAuthorize_refused_no_effect` — A program the checker refuses for the keyboard holds no keyboard permission, so each attempt it makes to load or run a keyboard program is refused and changes nothing.
- `boot_output` — In the run that the keyboard-echo boot image performs, the console shows exactly the typed keys: `lean ipc` and a newline.
- `boot_b_refused` — In that run, the program without permissions has all three of its attempts refused.
- `boot_a_observations` — In that run, the keyboard program's attempt to print directly is refused, and each key it sends to the server is accepted.
