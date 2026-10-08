/* Endpoint directory (#485), built from subjects/template and linked as
   subject C of the endpoint-directory image.

   The directory holds one endpoint capability per registered name, with the
   grant right, in its own capability slots.  Its slot 0 is the receive end of
   its request endpoint.  Every message it receives there is either a
   registration (a server delegated an endpoint capability under a name; the
   kernel installed it in one of the directory's slots) or a call (a client
   asks for a name, and the kernel holds a one-shot reply capability for it).

   For a call the directory attenuates the registered capability itself: it
   offers only the send right, and only if it holds both send and grant.  An
   unknown name is answered with no capability, which the kernel delivers as
   the typed miss.  The kernel checks every answer against the generated Lean
   witness (EndpointDirectory.directoryResolve) before installing anything.
   The transcript is scripts/expectations/endpoint-directory.transcript. */
#include <leanos/subject.h>

#define DIRECTORY_REQUESTS 0u    /* slot of the request endpoint (receive) */
#define DIRECTORY_ENTRIES 4u

/* Endpoint-rights bits (docs/endpoint-directory.md). */
#define RIGHT_SEND 1u
#define RIGHT_GRANT 4u

struct entry {
    uint64_t name;
    uint64_t slot;
    uint64_t rights;
};

/* In the subject's stack page above the stack (bss). */
static struct entry entries[DIRECTORY_ENTRIES];
static uint64_t entry_count;

static const struct entry *find(uint64_t name) {
    for (uint64_t i = 0; i < entry_count; ++i)
        if (entries[i].name == name) return &entries[i];
    return 0;
}

void subject_main(void) {
    uint64_t name = leanos_receive_word(DIRECTORY_REQUESTS);
    for (;;) {
        uint64_t info = leanos_message_info();
        if (LEANOS_MESSAGE_OP(info) == LEANOS_MESSAGE_REGISTER) {
            if (entry_count < DIRECTORY_ENTRIES && find(name) == 0) {
                entries[entry_count].name = name;
                entries[entry_count].slot = LEANOS_MESSAGE_SLOT(info);
                entries[entry_count].rights = LEANOS_MESSAGE_RIGHTS(info);
                entry_count = entry_count + 1;
            }
            name = leanos_receive_word(DIRECTORY_REQUESTS);
            continue;
        }
        /* A call: answer it through the reply capability and wait for the
           next request. */
        const struct entry *found = find(name);
        uint64_t source = LEANOS_NO_SLOT;
        uint64_t offered = 0;
        if (found != 0 && (found->rights & RIGHT_SEND) != 0 &&
            (found->rights & RIGHT_GRANT) != 0) {
            source = found->slot;
            offered = found->rights & RIGHT_SEND;
        }
        name = leanos_reply_receive(source, offered, DIRECTORY_REQUESTS);
    }
}
