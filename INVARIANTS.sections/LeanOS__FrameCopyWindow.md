# Frames cross through a window that shows the kernel only the requesting program's own pages

These theorems describe how the kernel copies a network frame into or out of a frame program's memory on a computer without the processor feature (SMAP) that normally keeps the kernel from touching user pages by accident. Instead of looking at user memory directly, the kernel switches for the length of one copy to a special set of page tables, a window, that shows it nothing of any program except the requesting program's own frame pages, as kernel-only, never-executable pages, and writable only when the kernel is copying a frame in. The model describes those page tables, the address translation through them and the copy as a sequence of single-byte reads or writes, and the theorems show that the window exposes only the requester's own frame pages, that every byte lands exactly where the earlier frame models say it should, that a copy changes nothing outside the requester's own window, and that the small generated function the kernel asks for the copy's starting address agrees with the kernel's frame checker. Nothing here proves that the booted kernel builds those page tables or performs the copy exactly as modelled.

- `windowRoot_outside` — Away from its reserved window slots, a window's page tables are exactly the closed page tables that show no program's pages.
- `windowRoot_alias` — Every page a window adds shows one of the requesting program's own frame pages, as a kernel-only, never-executable page whose write permission is the window's.
- `windowRoot_protected` — A window built from closed page tables shows a program's page only in a reserved slot, only as a kernel-only, never-executable view of the requester's own frame page, writable only in the window used for copying frames in.
- `windowRoot_other_absent` — In particular a window shows no page of any other program.
- `windowRoot_no_user` — No page a window shows of a program can be used by a program or executed.
- `covers_iff` — A range lies inside a memory window exactly when it starts at or after the window's start and ends at or before its end.
- `window_covers_iff` — The same holds for the memory window a window's geometry describes.
- `alias_succ` — The window address of the next byte is the window address of this byte plus one.
- `translate_alias` — The window address of every byte of the requester's frame pages leads to that very byte in physical memory.
- `writeBytes_cons` — Writing a list of bytes is writing its first byte and then the rest one place further on.
- `storeAll_alias` — Copying a frame in through the window, byte by byte, writes exactly the frame at the requested place, as the frame models say, without a fault.
- `storeAll_readonly` — Through the window used for copying frames out, no byte can be written at all.
- `readBytes_succ` — Reading several bytes is reading the first and then the rest one place further on.
- `loadAll_alias` — Copying a frame out through either window reads exactly the requested bytes, as the frame models say, without a fault.
- `covers_contains` — Every byte of a range that lies inside a memory window lies inside that window.
- `fetch_refines` — When physical memory matches what the shared-network model says each program holds, a copy-in the model accepts, done through the requester's window, does exactly what the model's copy-in does, and the match still holds afterwards.
- `fetch_footprint` — A copy-in changes only bytes in the requested range, inside the requester's own window, on pages that belong to the requester.
- `send_refines` — A copy-out the model accepts, done through the requester's window, reads exactly the frame the model puts in the outgoing slot.
- `network_fetch_refines` — The same exact copy-in holds for the earlier single-program network model.
- `network_send_refines` — The same exact copy-out holds for the earlier single-program network model.
- `geometryOk_nat` — The window shape the kernel's numbers must have means: page-aligned, one or two pages long, inside the first 16 MiB, with its reserved slots inside that range too.
- `geometryOk_spec` — Numbers with that shape describe a well-formed window whose end is the given end.
- `frameWindowOperand_ne_zero_iff` — The generated function the kernel asks for a copy's starting address returns an address exactly when the kernel's frame checker accepts the request and the window has the reviewed shape.
- `frameWindowOperand_alias` — The address it returns is the window address of the requested buffer, and the whole buffer lies inside the window.
- `ownerOf_request` — The request word the kernel builds for a frame program names that program as the window's owner.
- `frameWindowOperand_fetch` — For a frame program's copy-in, the function returns an address exactly when the model accepts, and copying in from that address writes exactly what the model's copy-in writes.
- `frameWindowOperand_send` — For a frame program's copy-out, the function returns an address exactly when the model accepts, and copying out from that address reads exactly the bytes the model reads.
- `frameWindowOperand_nonholder` — For a request naming a program that holds no frame permission, the function returns no address.
