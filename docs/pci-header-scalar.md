# Scalar PCI header validation

`PCIHeaderObservation.Scalar.status` validates a declared count, BDF and sixteen
raw dwords without constructing decoded objects. It preserves the reference
error order: invalid BDF, wrong count, non-dword, absent vendor, unsupported
layout. Endpoints and bridges return one. The general `status_eq_decode` theorem
proves exact status equivalence to the reference decoder for every sixteen-word
input, including malformed values; it is not limited to the retained capture.

`scripts/check-pci-header-scalar.sh` compiles the module, retains only the scalar
function, strips unused symbol-table entries and requires no undefined symbols
and exactly one defined symbol. It links that object without standard libraries
and executes 14,112 cases covering endpoint/bridge/multifunction layouts,
unsupported layouts, absent vendors, every non-dword position, BDF limits,
logical count errors and overlapping failures to check precedence. The ordinary
PCI header wrapper runs this check. Host GCC and pinned CI Clang 18 are checked.

This is an internal scalar function, not a new exported transport ABI. The
existing allocating header observer remains unchanged. The scalar status path
is a component for the native inventory bridge; complete identity/routing
projection, whole-snapshot binding and kernel integration remain required.
Neither a valid header nor an inventory match establishes DMA containment.
