# Oracle rows for spawning programs and loading them

The oracle rows for the spawn family on the stateful dispatcher, the ring-3 spawn system call, and the run-time loader, with the facts tying their expected words to the kernel model.

- `loader_vectors_expected` — The expected answers of the loader's rows are exactly the listed source answers and decisions.
- `spawn_syscall_vectors_expected` — The expected answers of the spawn system call's rows are exactly the listed replies, refusal words, and value words.
- `spawn_edge_vectors_cover` — Each spawn-family row sends its edge's state token and command words to the stateful dispatcher and expects that edge's reply and value words.
- `spawn_edge_vectors_match_model` — The words each spawn-family row expects are the encoded result of the kernel's spawn, child-control, or memory step on the complete kernel state the row's state token names, and that step ends in the state the reply names; so the hosted and booted checks of the generated code check the model's answer.
- `spawn_negative_vectors_reject` — Every hostile spawn-family encoding is answered with an error word and no value word, before any kernel step runs.
