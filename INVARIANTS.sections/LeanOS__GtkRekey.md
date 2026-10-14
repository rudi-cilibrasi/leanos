# The WiFi driver keeps working, and stays safe, when the access point changes its broadcast key

A WiFi access point protects broadcast traffic (such as the address questions computers ask everyone on the network) with a shared group key, and it replaces that key every so often. It sends each connected computer a key-change message, protected with that computer's own private key, which carries the new group key, a message counter and the number the new key's traffic will start counting from; the computer answers with a short acknowledgement. The new key takes turns between two key slots, numbered 1 and 2. LeanOS's WiFi driver handles this exchange itself, so the user-mode network programs never see a key. These theorems describe a model of what the driver does with each protected frame it receives — which key it uses, how it rejects replayed or forged frames, and how it installs a new group key — and show that the message counter only ever goes up across any number of key changes, that each key change is acknowledged at most once, that frame counters under each key only go up, and that after a key change broadcasts under the new key get through while frames under the old key, under stale key material or with an already-used counter are thrown away without changing anything. A fixed test sequence of fifteen frames, which changes the key from slot 1 to slot 2 and back, is shown to have exactly the outcomes the QEMU test expects. The driver program itself is checked against this model by simulation tests, not proved to follow it.

- `step_rejects` — A frame that does not decrypt under a known key, or whose counter is not above the last one accepted under that key, is dropped and changes nothing.
- `step_unknown` — A frame whose key slot number matches neither the private key nor the installed group key is dropped and changes nothing.
- `step_mic` — A frame protected with key material other than the key its slot number selects fails its integrity check, is dropped and changes nothing.
- `step_accepts` — A frame that decrypts and has a fresh counter is handled by its contents: a key-change message goes to the key-change logic, data goes to the network program, and in both cases its counter becomes the new floor for its key.
- `recordPn_replay` — Recording a frame's counter does not touch the key-change message counter.
- `recordPn_tk` — Recording a frame's counter does not touch the private key.
- `group_msg2` — A key-change message is acknowledged only if its message counter is above the last one accepted, its integrity check passes, its new key unpacks, and its slot number is a valid group-key slot; the acknowledgement repeats its counter, and the driver then holds exactly the new key, its slot number, its starting counter and the new message counter.
- `group_replay_mono` — Handling a key-change message never lowers the message counter.
- `step_replay_mono` — No received frame ever lowers the key-change message counter.
- `run_replay_mono` — Over any sequence of frames, the key-change message counter never goes down.
- `step_msg2` — The driver acknowledges a frame only when the frame decrypted with a fresh counter and carries a key-change message, and the result is exactly what the key-change logic produces.
- `msg2_replay` — Every acknowledgement repeats a message counter above the last one accepted, and that counter becomes the new last one.
- `run_msg2_gt` — Every acknowledgement later in a run repeats a message counter above the counter at the start of the run.
- `run_msg2_sorted` — Across any run, including any number of key changes, the message counters the driver acknowledges strictly increase.
- `msg2_once` — If the same key-change frame arrives again right after being acknowledged, whether a retransmission or a replay, it is not acknowledged again.
- `lastPn_recordPn` — After a frame's counter is recorded, the floor for that frame's key is exactly that counter.
- `deliver_pn` — A frame handed to the network program carried data, decrypted under the key its slot number selects, had a counter above the previous floor for that key, and its counter is now that key's floor.
- `group_pnTk` — Handling a key-change message never changes the private key's frame-counter floor.
- `recordPn_pnTk` — Recording an accepted frame's counter never lowers the private key's floor.
- `recordPn_pnGtk` — Recording an accepted frame's counter never lowers the group key's floor.
- `step_pnTk_mono` — The private key's frame-counter floor never goes down.
- `step_pnGtk_mono` — The group key's frame-counter floor never goes down, except when a new group key is installed, when it starts from the counter the access point announced.
- `msg2_installs` — Whenever the driver acknowledges a key change, the frame was a valid key-change message, and the driver now holds exactly the new key in its announced slot (1, 2 or 3, never the private key's slot 0) with the announced starting counter, while the private key is unchanged.
- `delivered_after_rekey` — After a key change, a broadcast protected with the new key under its slot number, with a counter above the announced starting counter, is decrypted and handed to the network program.
- `stale_id_dropped` — After a key change to another slot, a frame still using the old group-key slot is dropped and changes nothing.
- `stale_material_dropped` — After a key change, a frame using the new slot number but the old key material that slot used to hold fails its integrity check, is dropped and changes nothing.
- `replayed_pn_dropped` — A frame whose counter is at or below the last one accepted under its key is dropped and changes nothing, so replayed frames never reach the network program, before or after a key change.
- `scenario_outcomes` — The fixed fifteen-frame test sequence, which changes the group key from slot 1 to slot 2 and back to slot 1 and includes stale, replayed and forged frames, has exactly the outcomes the QEMU test checks: four frames delivered, two key changes acknowledged and nine frames dropped for the stated reasons.
- `scenario_final` — After that test sequence the driver holds the third group key in slot 1, the message counter is 6, and the private and group frame-counter floors are 7 and 1.
