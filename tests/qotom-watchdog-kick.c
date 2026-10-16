/* The generated long-session watchdog check (issue #557,
   LeanOS.QotomWatchdogKick, leanos_qotom_watchdog_kick) from the lab's
   freestanding native-pci.o, against an independent C statement of
   kickDecide_zero_iff and its refusal order, over every combination of
   boundary values; then a whole session driven as the lab kernel drives it
   (hardware/lab/qotom-network-subject.c.inc), which reloads on the link
   record and every 40th tick and never more than its budget.  Issue #567:
   the session-end check (leanos_qotom_watchdog_session_end, endDecide)
   against its own C statement over the same kicks and budgets, the kick
   check never refusing for a spent or invalid budget while the session is
   served, and sessions whose records outlast the budget (the hardware run
   of #567 among them) ending at the budget, before any such refusal. */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include "boundary-abi.h"

#define CAP_KICKS 92u

static uint64_t reference(uint64_t event, uint64_t ticks, uint64_t kicks, uint64_t budget,
                          uint64_t count, uint64_t timer) {
    if (budget == 0 || budget > CAP_KICKS) return 3;
    if (kicks >= budget) return 2;
    if (count != 0) return 4;
    if (timer != 120) return 5;
    if (event == 1) return kicks == 0 ? 0 : 1;
    if (event == 2) return ticks >= 40 ? 0 : 1;
    return 6;
}

static uint64_t budget_of(uint64_t seconds) { return 2 + (seconds + 39) / 40; }

static uint64_t end_reference(uint64_t kicks, uint64_t budget) {
    if (budget == 0 || budget > CAP_KICKS) return 1;
    return kicks >= budget ? 1 : 0;
}

/* A session as the lab kernel drives it: before each record the end check
   (when `end_check`), then the link record or a tick.  Returns the reloads
   made; reports the ticks the driver yielded before the session ended, how
   it ended and whether any decision refused for a spent budget (2) or an
   invalid one (3).  Fails (returns UINT64_MAX) on any other surprise. */
static uint64_t drive(uint64_t budget, uint64_t records, int end_check, uint64_t *taken,
                      int *budget_end, int *exhausted) {
    uint64_t made = 0, since = 0;
    *taken = 0; *budget_end = 0; *exhausted = 0;
    for (uint64_t record = 0; record <= records; ++record) {
        if (end_check) {
            uint64_t e = leanos_qotom_watchdog_session_end(made, budget);
            if (e != end_reference(made, budget)) return UINT64_MAX;
            if (e == 1) { *budget_end = 1; return made; }
        }
        uint64_t event = record == 0 ? 1 : 2;
        if (event == 2) { ++since; ++*taken; }
        uint64_t d = leanos_qotom_watchdog_kick(event, since, made, budget, 0, 120);
        if (d == 2 || d == 3) *exhausted = 1;
        if (d == 0) {
            if (event == 2 && since < 40) return UINT64_MAX;
            ++made;
            since = 0;
        } else if (d != 1 && d != 2 && d != 3) {
            return UINT64_MAX;
        }
    }
    return made;
}

int main(void) {
    static const uint64_t events[] = {0, 1, 2, 3, UINT64_MAX};
    static const uint64_t ticks[] = {0, 1, 39, 40, 41, 1000, UINT64_MAX};
    static const uint64_t kicks[] = {0, 1, 24, 25, 46, 47, 91, 92, 93, UINT64_MAX};
    static const uint64_t budgets[] = {0, 1, 25, 47, 91, 92, 93, 1000, UINT64_MAX};
    static const uint64_t counts[] = {0, 1, 0x800, 0x200, UINT64_MAX};
    static const uint64_t timers[] = {120, 4, 119, 121, 0x478, UINT64_MAX};
    unsigned cases = 0, admitted = 0, served = 0, end_cases = 0;
    for (unsigned e = 0; e < sizeof events / sizeof *events; ++e)
    for (unsigned t = 0; t < sizeof ticks / sizeof *ticks; ++t)
    for (unsigned k = 0; k < sizeof kicks / sizeof *kicks; ++k)
    for (unsigned b = 0; b < sizeof budgets / sizeof *budgets; ++b)
    for (unsigned c = 0; c < sizeof counts / sizeof *counts; ++c)
    for (unsigned r = 0; r < sizeof timers / sizeof *timers; ++r) {
        uint64_t got = leanos_qotom_watchdog_kick(events[e], ticks[t], kicks[k], budgets[b],
                                                  counts[c], timers[r]);
        uint64_t want = reference(events[e], ticks[t], kicks[k], budgets[b], counts[c],
                                  timers[r]);
        ++cases;
        admitted += got == 0;
        /* Issue #567: while the session is served the kick check never
           refuses for a spent or an invalid budget (serving_never_exhausted). */
        if (leanos_qotom_watchdog_session_end(kicks[k], budgets[b]) == 0) {
            ++served;
            if (got == 2 || got == 3) {
                fprintf(stderr, "watchdog kick case %u refused a served session: %" PRIu64 "\n",
                        cases, got);
                return 1;
            }
        }
        if (got != want) {
            fprintf(stderr, "watchdog kick case %u: event=%" PRIu64 " ticks=%" PRIu64
                    " kicks=%" PRIu64 " budget=%" PRIu64 " count=%" PRIu64 " timer=%" PRIu64
                    " got %" PRIu64 " want %" PRIu64 "\n", cases, events[e], ticks[t],
                    kicks[k], budgets[b], counts[c], timers[r], got, want);
            return 1;
        }
    }
    static const uint64_t end_kicks[] = {0, 1, 24, 25, 46, 47, 90, 91, 92, 93, 1000,
                                         UINT64_MAX - 1, UINT64_MAX};
    static const uint64_t end_budgets[] = {0, 1, 2, 25, 47, 91, 92, 93, 1000, UINT64_MAX};
    for (unsigned k = 0; k < sizeof end_kicks / sizeof *end_kicks; ++k)
    for (unsigned b = 0; b < sizeof end_budgets / sizeof *end_budgets; ++b) {
        ++end_cases;
        uint64_t got = leanos_qotom_watchdog_session_end(end_kicks[k], end_budgets[b]);
        if (got != end_reference(end_kicks[k], end_budgets[b])) {
            fprintf(stderr, "session end case kicks=%" PRIu64 " budget=%" PRIu64 " got %" PRIu64
                    "\n", end_kicks[k], end_budgets[b], got);
            return 1;
        }
    }
    if (budget_of(3600) != CAP_KICKS || budget_of(1800) != 47 || budget_of(900) != 25) {
        fprintf(stderr, "watchdog kick budget formula differs from budgetOf\n");
        return 1;
    }
    /* A 30-minute session as the kernel drives it: the link record, then a
       tick per second; the session's records outlast its budget, and the
       kernel ends it right after the last reload, the 1840th tick. */
    uint64_t budget = budget_of(1800), taken = 0;
    int budget_end = 0, exhausted = 0;
    uint64_t made = drive(budget, 7200, 1, &taken, &budget_end, &exhausted);
    if (made != budget || taken != 40 * (budget - 1) || !budget_end || exhausted) {
        fprintf(stderr, "session made %" PRIu64 " reloads over %" PRIu64 " ticks, budget %"
                PRIu64 "\n", made, taken, budget);
        return 1;
    }
    /* The hardware run of issue #567: a one-hour image whose driver yielded
       3800 ticks.  Without the end check the kick check refused for the
       spent budget (WATCHDOG-KICK stopped reason=2) and FINAL never came;
       with it the session ends at the 92nd reload, after 3640 ticks. */
    made = drive(CAP_KICKS, 3800, 0, &taken, &budget_end, &exhausted);
    if (made != CAP_KICKS || !exhausted || budget_end) return 1;
    made = drive(CAP_KICKS, 3800, 1, &taken, &budget_end, &exhausted);
    if (made != CAP_KICKS || taken != 3640 || !budget_end || exhausted) {
        fprintf(stderr, "issue 567 session made %" PRIu64 " reloads over %" PRIu64 " ticks\n",
                made, taken);
        return 1;
    }
    /* The earlier hour-long runs: 3495 ticks, 88 reloads, the window ends
       the session.  And every session length up to twice the longest
       window, for every valid budget: never a spent-budget refusal, and the
       session ends at its budget exactly when its ticks outlast it. */
    made = drive(CAP_KICKS, 3495, 1, &taken, &budget_end, &exhausted);
    if (made != 88 || taken != 3495 || budget_end || exhausted) return 1;
    unsigned sessions = 0;
    for (uint64_t b = 1; b <= CAP_KICKS; ++b)
        for (uint64_t records = 0; records <= 7200; records += 7) {
            made = drive(b, records, 1, &taken, &budget_end, &exhausted);
            int outlast = records > 40 * (b - 1);
            uint64_t want = records / 40 + 1 < b ? records / 40 + 1 : b;
            ++sessions;
            if (made != want || exhausted || budget_end != outlast) {
                fprintf(stderr, "session budget=%" PRIu64 " records=%" PRIu64 " made %" PRIu64
                        " end %d exhausted %d\n", b, records, made, budget_end, exhausted);
                return 1;
            }
        }
    printf("Qotom watchdog kick: %u cases (%u admitted, %u served without a spent-budget "
           "refusal) agree; %u session-end cases agree; a 1800 s session ends at its budget %"
           PRIu64 " after 1840 ticks; the issue 567 run ends at 92 reloads after 3640 ticks; "
           "%u sessions never exhaust their budget\n", cases, admitted, served, end_cases,
           budget_of(1800), sessions);
    return 0;
}
