# A frame server program that hands out memory within budgets

Instead of the kernel deciding who gets memory, one ordinary program, the frame server, holds a fixed collection of memory pages (its pool) and decides who gets which page. Each other program has a budget: the most pages it may hold at once. The kernel no longer makes these choices; it only checks each decision the server makes, carries out the ones that pass exactly as stated, and wipes every page clean before handing it out. These theorems guarantee that the kernel's role really is just checking, that no program ever holds more pages than its budget, that nobody gains authority they did not have, and that a page handed back by one program is wiped before any program can see it again.

- `decide_rejected_unchanged` — When the kernel refuses one of the server's decisions, nothing in the system changes.
- `decide_accepted_effect` — When the kernel accepts one of the server's decisions, the decision passed the check and has exactly the effect it names.
- `kernel_only_checks` — Every decision of the server is either refused with no effect or carried out exactly as the server stated it; the kernel never picks a page, a program, permissions or a reason itself.
- `check_server` — The kernel only ever accepts a decision that comes from the frame server.
- `granted_exact` — When a page is handed out, the server asked for it, the page is from the server's pool and was free, the permissions are within the pool's, and the receiving program was under its budget; exactly that page goes to exactly that program, wiped clean, and nothing else changes hands.
- `refused_truthful` — When the server turns a request down, nothing is handed out, and the stated reason (budget used up, or no free page) is true.
- `serverPolicy_accepted` — The straightforward server policy (give the first free page while the program is under budget, otherwise refuse with the true reason) is never overruled by the kernel's check.
- `countP_update` — Bookkeeping: changing one item of a list without repeats from "not counted" to "counted" raises the count by exactly one.
- `usage_grant` — Bookkeeping: handing out one free page raises the receiving program's page count by one and leaves everyone else's unchanged.
- `usage_le_of_subset` — Bookkeeping: if a program holds no page after a step that it did not hold before, its page count did not go up.
- `effect_revoke_grant` — Bookkeeping: taking away a program's budget clears exactly the pages that program held.
- `holds_revoke` — After a program's budget is taken away it holds no page, and every other program holds exactly the pages it held before.
- `holds_reclaim` — Taking one page back affects only that page; every program holds every other page exactly as before.
- `step_preserves_invariant` — Whatever the server decides and whatever programs write, the system stays in good order: pages come only from the pool with permissions within the pool's, every program is within its budget, and every page a program holds but has not yet written to is all zeros.
- `budget_respected` — No program ever holds more pages than its budget allows.
- `decide_preserves_authority` — No decision changes which program is the server, which pages are in its pool or what permissions the pool carries, and no decision ever raises a budget.
- `no_amplification` — No step gives anyone more authority: the server, its pool and the pool's permissions stay fixed, no budget grows, and every handed-out page stays within the pool and its permissions.
- `grant_publishes_scrubbed` — A program that has just been handed a page reads zero everywhere in it, whatever the page held before, including another program's data.
- `release_preserves_bytes` — Taking a page back does not itself wipe it; the wipe happens when the page is next handed out.
- `revoke_retires` — When a program's budget is taken away, it is left with no pages and a budget of zero.
- `read_unwritten_zero` — Any program reading a page it holds but has not written to reads zero, so a page given back by someone else is always wiped before it can be seen again.
- `ofNat_le_iff` — Bookkeeping: comparing two small counts as machine words gives the same answer as comparing them as numbers.
- `ofNat_lt_iff` — Bookkeeping: the strict version of the same comparison fact.
- `grant_cases` — Bookkeeping: a page is either handed out to someone or free.
- `frameServerCheck_agrees` — The small numeric checker the running kernel consults gives exactly the model's answer for every possible decision of the server in every possible state.
- `decide_not_server` — A decision from any program other than the server is refused and changes nothing.
- `boot_grant_a` — In the demonstrated run, the first program's request is answered with the first pool page, and the numeric checker agrees.
- `boot_written_a` — In the demonstrated run, the first program writes its marker to the first and last byte of its page and reads it back.
- `boot_refuse_a` — In the demonstrated run, the first program's second request is refused because its budget of one page is used up, even though another page is free, and the numeric checker gives the same typed refusal.
- `boot_revoke_a` — In the demonstrated run, taking away the first program's budget leaves it with no page and a budget of zero, while the page still holds its marker.
- `boot_grant_b` — In the demonstrated run, the second program, with a larger budget, is handed the same page and reads zero where the first program's marker was, and the first program can no longer read it.
- `boot_hostile_refused` — The numeric checker refuses every hostile decision the running kernel tests at start-up: a page outside the pool, a page already in use, too many or no permissions, a request over budget, a false refusal, taking back a page the program does not hold, and an unknown decision.
- `ofNat_inj` — Bookkeeping: two small numbers that are equal as machine words are equal as numbers.
- `frameServerView_agrees` — The small numeric function the running kernel uses to describe a page to the checker (outside the pool, free, held by this program, or held by another) gives exactly the model's description, whatever the state.
- `frameServerView_pool` — For a "no free page" refusal, that function reports a free page exactly when the model has one.
- `boot_view_words` — The page descriptions the running kernel computes in the demonstrated run, and at start-up, are the expected ones.
