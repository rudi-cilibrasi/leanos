# Render the Lean-emitted export inventory (leanos-abi) as the generated
# boundary-abi.h prototype header.  Scalar exports become uint64_t prototypes
# unconditionally; the hosted-only exports that take Lean objects are emitted
# only when the including harness defines LEANOS_BOUNDARY_ABI_OBJECTS after
# including lean.h.
function fail(message) {
  print "error: " message > "/dev/stderr"
  failed = 1
  exit 2
}
function prototype(symbol, params,   line, i, n, out, piece) {
  n = split(params, p, ",")
  out = "uint64_t " symbol "("
  line = out
  for (i = 1; i <= n; i++) {
    piece = p[i] ((i < n) ? "," : ");")
    if (length(line) + length(piece) + (i > 1) > 79) {
      out = out "\n    " piece
      line = "    " piece
    } else {
      out = out (i > 1 ? " " : "") piece
      line = line (i > 1 ? " " : "") piece
    }
  }
  return out
}
BEGIN { FS = "\t"; scalars = 0; objects = 0 }
NR == 1 {
  if ($0 != "leanos-abi\t1")
    fail("unexpected boundary abi schema: " $0)
  next
}
$1 == "source-revision" { next }
$1 == "export" || $1 == "object-export" {
  if (NF != 5 || $2 !~ /^leanos_[a-z0-9_]+$/ || $4 == "" || $5 == "")
    fail("malformed generated export row: " $0)
  if ($2 in seen)
    fail("duplicate generated export symbol: " $2)
  seen[$2] = 1
  if ($1 == "export") {
    if ($3 !~ /^[0-9]+$/ || $3 + 0 > 128)
      fail("malformed generated export arity: " $2)
    params = ""
    for (i = 0; i < $3 + 0; i++)
      params = params (i ? "," : "") "uint64_t"
    if ($3 + 0 == 0)
      params = "void"
    scalar_symbol[scalars] = $2
    scalar_arity[scalars] = $3 + 0
    scalar_params[scalars] = params
    scalars++
  } else {
    n = split($3, shape, ",")
    if (n < 2 || shape[n] != "u64")
      fail("unsupported generated object export result: " $2)
    params = ""
    for (i = 1; i < n; i++) {
      if (shape[i] == "u64") type = "uint64_t"
      else if (shape[i] == "ByteArray") type = "lean_object *"
      else fail("unsupported generated object export parameter: " $2 " " shape[i])
      params = params (i > 1 ? "," : "") type
    }
    object_symbol[objects] = $2
    object_params[objects] = params
    objects++
  }
  next
}
{ fail("unexpected boundary abi row: " $0) }
END {
  if (failed)
    exit 2
  if (scalars == 0)
    fail("generated boundary abi lists no scalar exports")
  print "/* Generated from the LeanOS @[export] attributes; do not edit. */"
  print "#ifndef LEANOS_BOUNDARY_ABI_H"
  print "#define LEANOS_BOUNDARY_ABI_H"
  print ""
  print "#include <stdint.h>"
  print ""
  for (i = 0; i < scalars; i++)
    print prototype(scalar_symbol[i], scalar_params[i])
  print ""
  print "#define LEANOS_BOUNDARY_SCALAR_EXPORTS(X) \\"
  for (i = 0; i < scalars; i++)
    printf "  X(%s, %d)%s\n", scalar_symbol[i], scalar_arity[i], (i + 1 < scalars ? " \\" : "")
  printf "#define LEANOS_BOUNDARY_SCALAR_EXPORT_COUNT %dU\n", scalars
  print ""
  print "#ifdef LEANOS_BOUNDARY_ABI_OBJECTS"
  for (i = 0; i < objects; i++)
    print prototype(object_symbol[i], object_params[i])
  printf "#define LEANOS_BOUNDARY_OBJECT_EXPORT_COUNT %dU\n", objects
  print "#endif"
  print ""
  print "#endif"
}
