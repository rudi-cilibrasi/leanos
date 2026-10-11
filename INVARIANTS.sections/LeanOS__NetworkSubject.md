# The network program reaches only its own frame buffer

These theorems describe how network frames travel between the WiFi driver and a separate network program in user mode, which answers ARP, ping and UDP echo requests. A frame is too big to fit in one message, so the kernel copies it: the driver's device program leaves each received frame in a fixed slot, the driver program only tells the network program its length, and the network program asks the kernel to copy the frame into a buffer of its own and to copy its reply back out. The model says who may ask for a copy and where the kernel may write, and the theorems show that frames cross only through this path, that only the network program can use it, that the kernel writes frame bytes nowhere but inside the network program's own memory, and that the network program cannot touch any device. The kernel checks each copy request with a small generated checker that these theorems tie to the model; no theorem here says the booted code follows the model step by step.

- `nonholder_refused` — A request to copy a frame in or out from any program other than the network program is refused and changes nothing.
- `writeBytes_outside` — Writing a run of bytes into memory leaves every address outside that run unchanged.
- `step_mem_changed` — When one step changes a byte of some program's memory, either that program stored to its own memory, or the kernel copied a frame into the network program inside its own window.
- `run_mem_outside_window` — Over any run, a byte that its owner never stored to changes only if it lies inside the network program's own window: the kernel copies no frame byte anywhere else.
- `run_driver_mem` — In particular the driver program's memory changes only by its own stores: it never receives a frame byte from the kernel.
- `step_rx_changed` — The slot holding a received frame changes only when the driver's device program delivers a new frame.
- `step_tx_changed` — The slot holding a reply changes only when the device program takes it, or when the network program's accepted send places in it exactly the bytes of a range inside its own window.
- `network_no_device_effects` — The network program is never given a device permission, so every attempt it makes to load or run a device program is refused and leaves every device exactly as it was.
- `deviceAuthorize_network` — The generated device checker the kernel uses refuses the network program every device.
- `rangeOk_iff` — The checker's overflow-free range test says yes exactly when the requested bytes lie wholly inside the window.
- `gt1514_iff` — A length is over the largest Ethernet frame exactly when it exceeds 1514 bytes.
- `lt14_iff` — A length is under the smallest Ethernet frame exactly when it is below 14 bytes.
- `frameCopyDecide_fetch_iff` — The checker's decision accepts a copy-in exactly from the network program, with a frame waiting, of at most a full frame, into a range inside its window.
- `frameCopyDecide_send_iff` — The checker's decision accepts a copy-out exactly from the network program, with no reply already waiting, of a valid frame length, from a range inside its window.
- `frameCopyDecide_fetch` — For the network program, the checker's decision on a copy-in agrees exactly with the model's rule.
- `frameCopyDecide_send` — For the network program, the checker's decision on a copy-out agrees exactly with the model's rule.
- `frameCopyDecide_nonholder` — The checker's decision refuses any other program whatever it asks, naming it as not the holder.
- `frameCopyCheck_fetchRequest` — The exported checker reads a copy-in request word as the copy-in operation with the right waiting-frame flag.
- `frameCopyCheck_sendRequest` — The exported checker reads a copy-out request word as the copy-out operation with the right waiting-reply flag.
- `frameCopyCheck_fetch` — The checker built into the kernel accepts the network program's copy-in exactly when the model does.
- `frameCopyCheck_send` — The checker built into the kernel accepts the network program's copy-out exactly when the model does.
- `frameCopyCheck_nonholder` — The checker built into the kernel refuses every other program, whatever it asks.
