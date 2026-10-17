# The loader and the whole system, side by side

This section puts the loader (the program that fills a new child's memory from a checked program file) next to the model of the whole system, the way the running kernel uses them together. It shows that when a load fails, undoing the loader and ending the child in the system together put everything back as it was before the child was created, and that once the child is started, its one message can only reach the channel its parent gave it.

- `step_constants` — A loader request never changes the reserved area, the file's plan, or the file's bytes.
- `step_child` — A loader request either keeps the child being loaded or discards it.
- `rolledBack_live` — A load is undone only for the live child the request names.
- `rollback_congr` — The "nothing loaded" state depends only on the reserved area, the plan and the file.
- `loaderStep_tracks` — Each loader request keeps the bookkeeping that ties the loader to the system: the system is untouched while the child is being loaded, or the loader has no child.
- `runLoader_tracks` — The same holds after any number of loader requests.
- `grantSteps_composite` — Giving frames through the side-by-side model does exactly what giving frames does in the system model.
- `grantSteps_loader` — Giving frames only adds to the loader's count of the child's frames.
- `joint_rollback_restores` — Create a child, give it frames, run any loader requests, and let one fail: the loader is back exactly where it was before the child was created, and the system has every authority and resource record it had before the child was created.
- `childSendStep_trace` — The started child's send in the side-by-side model is exactly the child-send step of the system model.
- `joint_child_send_confined` — After a child is created, given frames and started, the subject that sends is that child, and an accepted send reaches only the channel the parent gave it, with exactly the rights the parent asked for, and changes nothing else.
