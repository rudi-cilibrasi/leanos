/* Synthetic boundary-size fixtures, separate from captured firmware rows. */
static lean_object *root_test_bytes(size_t size) {
  lean_object *bytes = lean_alloc_sarray(1, size, size);
  if (size) memset(lean_sarray_cptr(bytes), 0, size);
  return bytes;
}

static void test_root_adapter_bounds(void) {
  for (uint64_t code = 300; code <= 305; ++code) {
    lean_object *info = root_test_bytes(code == 305 ? 65537 : 0);
    lean_object *root = root_test_bytes(code == 302 ? 65536 : code == 303 ? 65537 : 0);
    lean_object *addresses = lean_mk_empty_array();
    lean_object *tables = lean_mk_empty_array();
    size_t count = code == 300 ? 257 : code == 301 ? 1 : code == 302 ? 16 : 0;
    for (size_t i = 0; i < count; ++i) {
      addresses = lean_array_push(addresses, lean_box_uint64(i));
      if (code == 302) tables = lean_array_push(tables, root_test_bytes(65536));
    }
    uint64_t executing = code == 304 ? UINT64_C(0x100000000) : 0;
    for (uint64_t word = 0; word < 5; ++word) {
      lean_inc(info); lean_inc(root); lean_inc(addresses); lean_inc(tables);
      uint64_t actual = leanos_boot_captured_root_query(0x36d76289, 0x1000,
        info, root, 0, addresses, tables, executing, word);
      uint64_t expected = word == 0 ? 1 : word == 1 ? 2 : word == 2 ? code : 0;
      if (actual != expected) {
        fprintf(stderr, "root adapter bound %llu word %llu: expected %llu, got %llu\n",
          (unsigned long long)code, (unsigned long long)word,
          (unsigned long long)expected, (unsigned long long)actual);
        exit(1);
      }
    }
    lean_dec(info); lean_dec(root); lean_dec(addresses); lean_dec(tables);
  }
  puts("Captured-root adapter bounds passed: six fixtures, thirty result words");
}
