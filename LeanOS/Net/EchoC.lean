import LeanOS.Net.Echo

/-!
# The generated C of the network subject's responder (issue #450)

`reply` of `LeanOS.Net.Echo` at the C hooks. This module is compiled to C
only (`lean --c`) for the network subject (`subjects/net/`), which defines
`net_gen_value`, `net_gen_rd8` and `net_gen_wr8` over its frame buffer; no
hosted executable imports it.
-/
namespace LeanOS.Net.Echo

-- The generated C runs in a ring-3 subject with no module initializer.
set_option compiler.extract_closed false

@[extern "net_gen_value"] opaque cValue (t x : UInt64) : UInt64
@[extern "net_gen_rd8"] opaque cRd (t : UInt64) (off : UInt32) : UInt64
@[extern "net_gen_wr8"] opaque cWr (t : UInt64) (off v : UInt32) : UInt64

/-- The C hooks: the token is the `uint64_t` each hook returns. -/
instance instHooksC : Hooks UInt64 where
  val t := t
  withVal := cValue
  rd := cRd
  wr := cWr

/-- The generated responder: `reply` at the C hooks. `t` is the initial token
(callers pass 0); the result is the reply's length, 0 for none. `mac` holds
the 48-bit hardware address and `ip` the IPv4 address in its low 32 bits. -/
@[export leanos_net_reply]
def netReply (t len mac ip : UInt64) : UInt64 :=
  reply t len.toUInt32 mac ip.toUInt32

end LeanOS.Net.Echo
