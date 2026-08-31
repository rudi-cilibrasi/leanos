# Bootstrap sanity check

This file exists to confirm that the project's proof tooling is wired up correctly, not to say anything about the operating system itself. It defines a tiny "add one, but never past a limit" counter and proves the one promise that counter makes.

- `boundedSuccessor_le` — Adding one to a value while a cap is in place never produces a result above the cap, no matter what the value or the cap is.
