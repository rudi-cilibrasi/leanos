# Render `lake exe leanos-spawn-allocator` output into spawn-allocator.h (#575).
BEGIN {
  FS = "\t"
  print "/* Generated from LeanOS.SpawnAllocatorVectors; do not edit. */"
  print "struct spawn_allocator_vector { char kind; unsigned long long state[13], input[5], reply, value, next[13]; };"
  count = 0
}
function words(text, expected, name,    n, w, i, out) {
  n = split(text, w, ",")
  if (n != expected) {
    printf "error: spawn-allocator %s has %d words, not %d\n", name, n, expected > "/dev/stderr"
    exit 2
  }
  out = ""
  for (i = 1; i <= n; i++) {
    if (w[i] !~ /^[0-9]+$/) {
      printf "error: spawn-allocator %s word is not a number: %s\n", name, w[i] > "/dev/stderr"
      exit 2
    }
    out = out (i > 1 ? "," : "") w[i] "ULL"
  }
  return out
}
NR == 1 {
  if ($0 != "leanos-spawn-allocator\t1") {
    print "error: unexpected spawn-allocator corpus header" > "/dev/stderr"
    exit 2
  }
  next
}
$1 == "expected-seed" {
  expected_seed = words($2, 13, "expected seed")
  next
}
$1 ~ /^[0-9]+$/ {
  if ($1 != count || ($2 != "s" && $2 != "k") || $5 !~ /^[0-9]+$/ || $6 !~ /^[0-9]+$/) {
    print "error: malformed spawn-allocator vector: " $1 > "/dev/stderr"
    exit 2
  }
  if (!started) {
    print "static const struct spawn_allocator_vector spawn_allocator_vectors[] = {"
    started = 1
  }
  printf "{'%s',{%s},{%s},%sULL,%sULL,{%s}},\n", $2, words($3, 13, "state"), words($4, 5, "input"), $5, $6, words($7, 13, "next")
  count++
  next
}
{
  print "error: unexpected spawn-allocator corpus line: " $0 > "/dev/stderr"
  exit 2
}
END {
  if (!started || expected_seed == "") {
    print "error: incomplete spawn-allocator corpus" > "/dev/stderr"
    exit 2
  }
  print "};"
  print "#define SPAWN_ALLOCATOR_VECTOR_COUNT (sizeof(spawn_allocator_vectors)/sizeof(spawn_allocator_vectors[0]))"
  printf "static const unsigned long long spawn_allocator_seed_words[13] = {%s};\n", expected_seed
}
