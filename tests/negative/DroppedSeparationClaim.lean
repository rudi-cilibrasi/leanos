import LeanOS.SecurityClaims

open LeanOS

/- A separation claim cannot silently omit the distinct-frame conclusion. -/
example state first second page firstLeaf secondLeaf
    (hfirst : (X86PageTable.encode state first).leaf page = some firstLeaf)
    (hsecond : (X86PageTable.encode state second).leaf page = some secondLeaf) :
    X86PageTable.walk (X86PageTable.encode state first) page .read ≠
      X86PageTable.walk (X86PageTable.encode state second) page .read := by
  exact SecurityClaims.page_table_distinct_spaces_separated state first second page
    firstLeaf secondLeaf hfirst hsecond
