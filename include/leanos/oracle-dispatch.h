#ifndef LEANOS_ORACLE_DISPATCH_H
#define LEANOS_ORACLE_DISPATCH_H

#include <stdint.h>

#define LEANOS_ORACLE_CALL_2(symbol, vector) \
    symbol((vector)->words[0], (vector)->words[1])
#define LEANOS_ORACLE_CALL_4(symbol, vector) \
    symbol((vector)->words[0], (vector)->words[1], \
           (vector)->words[2], (vector)->words[3])
#define LEANOS_ORACLE_CALL_5(symbol, vector) \
    symbol((vector)->words[0], (vector)->words[1], \
           (vector)->words[2], (vector)->words[3], (vector)->words[4])
#define LEANOS_ORACLE_CALL_6(symbol, vector) \
    symbol((vector)->words[0], (vector)->words[1], \
           (vector)->words[2], (vector)->words[3], \
           (vector)->words[4], (vector)->words[5])
#define LEANOS_ORACLE_DISPATCH_CASE(id, symbol, arity) \
    case id: return LEANOS_ORACLE_CALL_##arity(symbol, vector);

#ifndef LEANOS_ORACLE_DISPATCH_ATTRIBUTES
#define LEANOS_ORACLE_DISPATCH_ATTRIBUTES inline
#define LEANOS_ORACLE_DISPATCH_ATTRIBUTES_LOCAL 1
#endif

static LEANOS_ORACLE_DISPATCH_ATTRIBUTES uint64_t
leanos_oracle_dispatch(const struct oracle_vector *vector) {
    switch (vector->adapter) {
        LEANOS_ORACLE_ADAPTERS(LEANOS_ORACLE_DISPATCH_CASE)
    default:
        return UINT64_MAX;
    }
}

#ifdef LEANOS_ORACLE_DISPATCH_ATTRIBUTES_LOCAL
#undef LEANOS_ORACLE_DISPATCH_ATTRIBUTES_LOCAL
#undef LEANOS_ORACLE_DISPATCH_ATTRIBUTES
#endif
#undef LEANOS_ORACLE_DISPATCH_CASE
#undef LEANOS_ORACLE_CALL_6
#undef LEANOS_ORACLE_CALL_5
#undef LEANOS_ORACLE_CALL_4
#undef LEANOS_ORACLE_CALL_2

#endif
