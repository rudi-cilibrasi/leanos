# Checking what operations leave behind, not just what they answer

The test corpus elsewhere compares the kernel's answer words. An answer can say that a memory page was handed out without saying whether the page was wiped first, and it can say that a permission was copied or withdrawn without showing the permission table afterwards. This file adds a second, smaller test corpus that compares the state left behind: a fingerprint of a page's bytes with a flag for "some byte is not zero", and the exact contents of individual permission-table entries, after the same canonical scenarios. It is run only on the build machine, never inside a boot image.

- `poststate_shape` — The after-state test corpus contains exactly 18 cases.
