# Isolation, cleanup, and stale handles at the spawn-family states

This section checks, on the complete kernel states the spawn family's dispatcher table names, what spawning, giving memory, ending a child, and reusing slots leave behind.

- `boundary_checks_pass` — On the boot plan the dispatcher uses: a new child holds exactly the send-only endpoint and its own empty address space, cannot use its parent's handle, cannot run, and has no memory; no state of the family changes anything the uninvolved subject holds; released and returned memory comes back free and wiped; ending a child removes its identity, permissions, address space, records, and memory charge and gives its memory back to the parent, which can then use it again under a never-used object identity; old memory and child handles stay refused after their slots are reused; a withdrawn and re-granted spawn permission gets a new generation; and the uninvolved subject, once running, sees none of the parent's children.
