# Render the Lean-emitted serial protocol vocabulary (leanos-oracle serial)
# as either the generated serial-protocol.h string-macro header (target=h) or
# the generated serial-protocol.sh shell fragment (target=sh).  Every row must
# carry a unique symbol and a prefix that is exactly "LEANOS/<version> <TAG>".
function fail(message) {
  print "error: " message > "/dev/stderr"
  failed = 1
  exit 2
}
BEGIN {
  FS = "\t"
  rows = 0
  families = 0
  if (target != "h" && target != "sh")
    fail("render-serial-protocol.awk needs -v target=h or -v target=sh")
}
NR == 1 {
  if ($0 != "leanos-serial-protocol\t1")
    fail("unexpected serial protocol schema: " $0)
  next
}
$1 == "source-revision" { next }
$1 == "family" {
  if (NF != 4 || $2 !~ /^[0-9]+$/ || $3 != "LEANOS_SERIAL_FAMILY_" $2 ||
      $4 != "LEANOS/" $2)
    fail("malformed generated serial family row: " $0)
  if ($3 in seen)
    fail("duplicate generated serial family: " $3)
  seen[$3] = 1
  family_symbol[families] = $3
  family_prefix[families] = $4
  families++
  next
}
$1 == "record" {
  if (NF != 5 || $2 !~ /^[0-9]+$/ || $3 !~ /^[A-Z][A-Z0-9-]*$/ ||
      $4 !~ /^LEANOS_SERIAL_[0-9]+_[A-Z][A-Z0-9_]*$/)
    fail("malformed generated serial record row: " $0)
  if ($5 != "LEANOS/" $2 " " $3)
    fail("generated serial record prefix does not denote its identity: " $4)
  if ($4 in seen)
    fail("duplicate generated serial record: " $4)
  seen[$4] = 1
  record_seen[$2 SUBSEP $3] = 1
  version[rows] = $2
  symbol[rows] = $4
  prefix[rows] = $5
  rows++
  next
}
$1 == "pre-admission-boot-record" {
  if (NF != 3 || $2 !~ /^[0-9]+$/ || $3 !~ /^[A-Z][A-Z0-9-]*$/ ||
      !(($2 SUBSEP $3) in record_seen))
    fail("malformed pre-admission boot record: " $0)
  if (($2 SUBSEP $3) in pre_admission_boot_seen)
    fail("duplicate pre-admission boot record: " $0)
  pre_admission_boot_seen[$2 SUBSEP $3] = 1
  pre_admission_boots++
  next
}
$1 == "pre-admission-record" {
  if (NF != 3 || $2 !~ /^[0-9]+$/ || $3 !~ /^[A-Z][A-Z0-9-]*$/ ||
      !(($2 SUBSEP $3) in record_seen))
    fail("malformed pre-admission phase record: " $0)
  if (($2 SUBSEP $3) in pre_admission_seen)
    fail("duplicate pre-admission phase record: " $0)
  pre_admission_seen[$2 SUBSEP $3] = 1
  pre_admission_records++
  next
}
$1 == "pre-admission-reason" {
  if (NF != 2 || $2 !~ /^[a-z0-9]+(-[a-z0-9]+)*$/)
    fail("malformed pre-admission rejection reason: " $0)
  if ($2 in rejection_seen)
    fail("duplicate pre-admission rejection reason: " $2)
  rejection_seen[$2] = 1
  rejection_reason[rejections++] = $2
  next
}
$1 == "pre-admission-bootalloc-reason" {
  if (NF != 2 || $2 !~ /^[a-z0-9]+(-[a-z0-9]+)*$/)
    fail("malformed pre-admission BOOTALLOC rejection reason: " $0)
  if ($2 in bootalloc_rejection_seen)
    fail("duplicate pre-admission BOOTALLOC rejection reason: " $2)
  bootalloc_rejection_seen[$2] = 1
  bootalloc_rejection_reason[bootalloc_rejections++] = $2
  next
}
{ fail("unexpected serial protocol row: " $0) }
END {
  if (failed)
    exit 2
  if (rows == 0)
    fail("generated serial protocol vocabulary is empty")
  if (target == "h") {
    print "/* Generated from LeanOS.SerialProtocol; do not edit. */"
    print "#ifndef LEANOS_SERIAL_PROTOCOL_H"
    print "#define LEANOS_SERIAL_PROTOCOL_H"
    print ""
    for (i = 0; i < families; i++)
      printf "#define %s \"%s\"\n", family_symbol[i], family_prefix[i]
    for (i = 0; i < rows; i++) {
      if (i == 0 || version[i] != version[i - 1])
        print ""
      printf "#define %s \"%s\"\n", symbol[i], prefix[i]
    }
    print ""
    printf "#define LEANOS_SERIAL_RECORD_COUNT %dU\n", rows
    printf "#define LEANOS_PRE_ADMISSION_REJECTION_REASON_COUNT %dU\n", rejections
    printf "#define LEANOS_PRE_ADMISSION_BOOTALLOC_REJECTION_REASON_COUNT %dU\n", bootalloc_rejections
    printf "#define LEANOS_PRE_ADMISSION_BOOT_RECORD_COUNT %dU\n", pre_admission_boots
    printf "#define LEANOS_PRE_ADMISSION_RECORD_COUNT %dU\n", pre_admission_records
    print ""
    print "#endif"
  } else {
    print "# Generated from LeanOS.SerialProtocol; do not edit.  Source this fragment."
    print ""
    for (i = 0; i < families; i++)
      printf "%s='%s'\n", family_symbol[i], family_prefix[i]
    for (i = 0; i < rows; i++) {
      if (i == 0 || version[i] != version[i - 1])
        print ""
      printf "%s='%s'\n", symbol[i], prefix[i]
    }
    print ""
    printf "LEANOS_SERIAL_RECORD_COUNT=%d\n", rows
    printf "LEANOS_PRE_ADMISSION_REJECTION_REASON_COUNT=%d\n", rejections
    printf "LEANOS_PRE_ADMISSION_BOOTALLOC_REJECTION_REASON_COUNT=%d\n", bootalloc_rejections
    printf "LEANOS_PRE_ADMISSION_BOOT_RECORD_COUNT=%d\n", pre_admission_boots
    printf "LEANOS_PRE_ADMISSION_RECORD_COUNT=%d\n", pre_admission_records
    print ""
    print "# The prefix of a record named by family and tag; unset for a record"
    print "# that is not in the vocabulary, which fails under set -u."
    print "leanos_serial() {"
    print "  local name=\"LEANOS_SERIAL_$1_${2//-/_}\""
    print "  printf '%s' \"${!name}\""
    print "}"
    print "# The same prefix with its slash escaped for a slash-delimited sed or awk"
    print "# regular expression."
    print "leanos_serial_re() {"
    print "  local value"
    print "  value=\"$(leanos_serial \"$1\" \"$2\")\""
    print "  printf '%s' \"${value//\\//\\\\/}\""
    print "}"
    print "leanos_serial_family_re() {"
    print "  local name=\"LEANOS_SERIAL_FAMILY_$1\" value"
    print "  value=\"${!name}\""
    print "  printf '%s' \"${value//\\//\\\\/}\""
    print "}"
  }
}
