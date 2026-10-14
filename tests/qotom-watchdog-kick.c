/* The generated long-session watchdog check (issue #557,
   LeanOS.QotomWatchdogKick, leanos_qotom_watchdog_kick) from the lab's
   freestanding native-pci.o, against an independent C statement of
   kickDecide_zero_iff and its refusal order, over every combination of
   boundary values; then a whole session driven as the lab kernel drives it
   (hardware/lab/qotom-network-subject.c.inc), which reloads on the link
   record and every 40th tick and never more than its budget. */
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

int main(void) {
    static const uint64_t events[] = {0, 1, 2, 3, UINT64_MAX};
    static const uint64_t ticks[] = {0, 1, 39, 40, 41, 1000, UINT64_MAX};
    static const uint64_t kicks[] = {0, 1, 24, 25, 46, 47, 91, 92, 93, UINT64_MAX};
    static const uint64_t budgets[] = {0, 1, 25, 47, 91, 92, 93, 1000, UINT64_MAX};
    static const uint64_t counts[] = {0, 1, 0x800, 0x200, UINT64_MAX};
    static const uint64_t timers[] = {120, 4, 119, 121, 0x478, UINT64_MAX};
    unsigned cases = 0, admitted = 0;
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
        if (got != want) {
            fprintf(stderr, "watchdog kick case %u: event=%" PRIu64 " ticks=%" PRIu64
                    " kicks=%" PRIu64 " budget=%" PRIu64 " count=%" PRIu64 " timer=%" PRIu64
                    " got %" PRIu64 " want %" PRIu64 "\n", cases, events[e], ticks[t],
                    kicks[k], budgets[b], counts[c], timers[r], got, want);
            return 1;
        }
    }
    if (budget_of(3600) != CAP_KICKS || budget_of(1800) != 47 || budget_of(900) != 25) {
        fprintf(stderr, "watchdog kick budget formula differs from budgetOf\n");
        return 1;
    }
    /* A 30-minute session as the kernel drives it: the link record, then a
       tick per second; the session's records outlast its budget. */
    uint64_t budget = budget_of(1800), session_ticks = 0, made = 0, since = 0;
    if (leanos_qotom_watchdog_kick(1, 0, 0, budget, 0, 120) != 0) return 1;
    made = 1;
    for (unsigned second = 1; second <= 7200; ++second) {
        ++session_ticks;
        ++since;
        uint64_t d = leanos_qotom_watchdog_kick(2, since, made, budget, 0, 120);
        if (d == 0) {
            if (since < 40) return 1;
            ++made;
            since = 0;
        } else if (d != 1 && d != 2) {
            return 1;
        }
    }
    if (made != budget || session_ticks != 7200) {
        fprintf(stderr, "session made %" PRIu64 " reloads, budget %" PRIu64 "\n", made, budget);
        return 1;
    }
    printf("Qotom watchdog kick: %u cases (%u admitted) agree; a 1800 s session's budget %"
           PRIu64 " bounds 7200 s of ticks\n", cases, admitted, budget);
    return 0;
}
