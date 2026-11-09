module

public import VerifiedGarbage.Spec.MdHashTable

/-!
# EMSA-PSS's encoding and its check with the hash functions as tables: sizes

Not trusted. `encode` and `checkEncoding` on AArch64, internal functions
that only verified code calls (`vg_rsa_pss_sign` and
`vg_rsa_pss_verify_precomputed`), have one copy for each index of the hash
function of the table of `MdHash`, which their callers choose by the
table's index. Their working space is 1088 words (`encScratch`):
MGF1's works at an offset in it.
-/

@[expose] public section

namespace VG.Proof.RsaPss

/-- The 64-bit words of working space `encode` and `checkEncoding` use. -/
def encScratch : Nat := 1088

end VG.Proof.RsaPss
