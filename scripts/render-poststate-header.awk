# Render `lake exe leanos-poststate` output into poststate.h (#476).
BEGIN {
  FS = "\t"
  print "/* Generated from LeanOS.PostStateProjection; do not edit. */"
  print "struct poststate_vector { unsigned adapter, argc; unsigned long long words[3], expected; const char *id; };"
  count = 0
}
NR == 1 {
  if ($0 != "leanos-poststate\t1") {
    print "error: unexpected post-state corpus header" > "/dev/stderr"
    exit 2
  }
  next
}
$1 == "adapter" {
  if ($2 !~ /^[0-9]+$/ || $3 !~ /^leanos_[a-z0-9_]+$/ || $4 !~ /^[23]$/ || ($2 in symbol)) {
    print "error: malformed post-state adapter: " $0 > "/dev/stderr"
    exit 2
  }
  symbol[$2] = $3
  arity[$2] = $4
  adapters++
  next
}
$1 ~ /^[0-9]+$/ {
  if (!started) {
    print "#define LEANOS_POSTSTATE_ADAPTERS(X) \\"
    for (i = 0; i < adapters; i++)
      printf "  X(%d, %s, %d)%s\n", i, symbol[i], arity[i], (i + 1 < adapters ? " \\" : "")
    print "static const struct poststate_vector poststate_vectors[] = {"
    started = 1
  }
  if (!($3 in symbol) || $5 !~ /^[0-9]+$/) {
    print "error: malformed post-state vector: " $2 > "/dev/stderr"
    exit 2
  }
  name = toupper($2)
  gsub(/[^A-Z0-9]/, "_", name)
  index_name[count] = name
  n = split($4, w, ",")
  if (n != arity[$3]) {
    print "error: post-state vector arity mismatch: " $2 > "/dev/stderr"
    exit 2
  }
  printf "{%s,%d,{", $3, n
  for (i = 1; i <= 3; i++)
    printf "%s%sULL", (i > 1 ? "," : ""), (i <= n ? w[i] : 0)
  printf "},%sULL,\"%s\"},\n", $5, $2
  count++
}
END {
  if (!started) {
    print "error: empty post-state corpus" > "/dev/stderr"
    exit 2
  }
  print "};"
  print "#define POSTSTATE_VECTOR_COUNT (sizeof(poststate_vectors)/sizeof(poststate_vectors[0]))"
  for (i = 0; i < count; i++)
    printf "#define POSTSTATE_INDEX_%s %d\n", index_name[i], i
}
