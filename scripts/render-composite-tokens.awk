# Render the Lean-emitted boundary vocabulary (leanos-oracle tokens) as the
# generated composite-tokens.h header.  Every row must carry a unique C name,
# a decimal word, and a C literal that denotes exactly that word.
function fail(message) {
  print "error: " message > "/dev/stderr"
  failed = 1
  exit 2
}
function literal_value(literal,   body, i, c, value, digits) {
  if (literal ~ /^UINT64_C\(0x[0-9a-f]+\)$/) {
    body = substr(literal, 12, length(literal) - 12)
    value = 0
    digits = "0123456789abcdef"
    for (i = 1; i <= length(body); i++) {
      c = substr(body, i, 1)
      value = value * 16 + index(digits, c) - 1
    }
    return value
  }
  if (literal ~ /^UINT64_C\([0-9]+\)$/)
    return substr(literal, 10, length(literal) - 10) + 0
  if (literal ~ /^[0-9]+U$/)
    return substr(literal, 1, length(literal) - 1) + 0
  fail("unsupported generated token literal: " literal)
}
BEGIN {
  FS = "\t"
  rows = 0
}
NR == 1 {
  if ($0 != "leanos-vocabulary\t1")
    fail("unexpected boundary vocabulary schema: " $0)
  next
}
$1 == "source-revision" { next }
$1 == "token" {
  if (NF != 5 || $2 !~ /^[A-Z]+$/ || $3 !~ /^[A-Z][A-Z0-9_]*$/ || $4 !~ /^[0-9]+$/)
    fail("malformed generated token row: " $0)
  if ($3 in seen)
    fail("duplicate generated token name: " $3)
  if (length($4) < 16 && literal_value($5) != $4 + 0)
    fail("generated token literal does not denote its word: " $3)
  seen[$3] = 1
  kind[rows] = $2
  name[rows] = $3
  literal[rows] = $5
  rows++
  next
}
{ fail("unexpected boundary vocabulary row: " $0) }
END {
  if (failed)
    exit 2
  if (rows == 0)
    fail("generated boundary vocabulary is empty")
  print "/* Generated from LeanOS.BoundaryVocabulary; do not edit. */"
  print "#ifndef LEANOS_COMPOSITE_TOKENS_H"
  print "#define LEANOS_COMPOSITE_TOKENS_H"
  print ""
  print "#include <stdint.h>"
  for (i = 0; i < rows; i++) {
    if (i == 0 || kind[i] != kind[i - 1]) {
      print ""
      print "/* " kind[i] " */"
    }
    printf "#define LEANOS_%s %s\n", name[i], literal[i]
  }
  print ""
  printf "#define LEANOS_COMPOSITE_TOKEN_COUNT %dU\n", rows
  print ""
  print "#endif"
}
