import LeanOS.Net.DhcpClient

/-!
# The generated C of the DHCP subject's client (issue #556)

`step` of `LeanOS.Net.DhcpClient` at the C hooks. This module is compiled to
C only (`lean --c`) for the DHCP subject (`subjects/dhcp/`), which defines
`dhcp_gen_value`, `dhcp_gen_rd8`, `dhcp_gen_wr8`, `dhcp_gen_ld` and
`dhcp_gen_st` over its frame buffer and its registers; no hosted executable
imports it.
-/
namespace LeanOS.Net.DhcpClient

-- The generated C runs in a ring-3 subject with no module initializer.
set_option compiler.extract_closed false

@[extern "dhcp_gen_value"] opaque cValue (t x : UInt64) : UInt64
@[extern "dhcp_gen_rd8"] opaque cRd (t : UInt64) (off : UInt32) : UInt64
@[extern "dhcp_gen_wr8"] opaque cWr (t : UInt64) (off v : UInt32) : UInt64
@[extern "dhcp_gen_ld"] opaque cLd (t : UInt64) (k : UInt32) : UInt64
@[extern "dhcp_gen_st"] opaque cSt (t : UInt64) (k : UInt32) (v : UInt64) : UInt64

/-- The C hooks: the token is the `uint64_t` each hook returns. -/
instance instHooksC : Hooks UInt64 where
  val t := t
  withVal := cValue
  rd := cRd
  wr := cWr
  ld := cLd
  st := cSt

/-- The generated client: `step` at the C hooks. `t` is the initial token
(callers pass 0) and `len` the record's length; the result is the length of
the frame left in the buffer to transmit, 0 for none. -/
@[export leanos_dhcp_step]
def dhcpStep (t len : UInt64) : UInt64 :=
  step t len.toUInt32

end LeanOS.Net.DhcpClient
