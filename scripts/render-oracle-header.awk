BEGIN {
  FS = "\t"
  print "/* Generated from LeanOS.Oracle; do not edit. */"
  print "struct oracle_vector { unsigned adapter, argc; unsigned long long words[6], expected; const char *id; };"
  print "static const struct oracle_vector oracle_vectors[] = {"
  vectorIndex = 0
}
$1 == "adapter-id" {
  if ($2 == "" || $3 !~ /^[0-9]+$/ || ($2 in adapterId)) {
    print "error: malformed or duplicate generated oracle adapter: " $2 > "/dev/stderr"
    exit 2
  }
  adapterId[$2] = $3
  next
}
$1 ~ /^[0-9]+$/ {
  if (!($3 in adapterId)) {
    print "error: unknown generated oracle adapter: " $3 > "/dev/stderr"
    exit 2
  }
  name = toupper($2)
  gsub(/[^A-Z0-9]/, "_", name)
  printf "#define ORACLE_INDEX_%s %d\n", name, vectorIndex++
  n = split($4, w, ",")
  printf "{%s,%d,{", adapterId[$3], n
  for (i = 1; i <= 6; i++)
    printf "%s%sULL", (i > 1 ? "," : ""), (i <= n ? w[i] : 0)
  printf "},%sULL,\"%s\"},\n", $5, $2
}
END {
  print "};"
  print "#define ORACLE_VECTOR_COUNT (sizeof(oracle_vectors)/sizeof(oracle_vectors[0]))"
}
