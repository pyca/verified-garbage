module

import VerifiedGarbage.Proof.Framework.QualifiedName
meta import VerifiedGarbage.Proof.Framework.QualifiedName

/-! # The names of a generic caller's instances (`VG.qualifiedName`) -/

namespace VG.Test.QualifiedName

open VG

-- Instances of a caller of several interfaces: one qualified part per
-- interface whose variant has a suffix; the baseline instance keeps the name.
#guard qualifiedName "vg_argon2" [("blake2b", ""), ("g", "")] == "vg_argon2"
#guard qualifiedName "vg_argon2" [("blake2b", ""), ("g", "_avx512")] ==
  "vg_argon2_g_avx512"
#guard qualifiedName "vg_argon2" [("blake2b", "_avx2"), ("g", "_avx512")] ==
  "vg_argon2_blake2b_avx2_g_avx512"
-- The same suffix in different interfaces gives different names.
#guard qualifiedName "vg_argon2" [("blake2b", "_avx2"), ("g", "")] ==
  "vg_argon2_blake2b_avx2"
#guard qualifiedName "vg_argon2" [("blake2b", ""), ("g", "_avx2")] ==
  "vg_argon2_g_avx2"
#guard qualifiedName "vg_argon2" [("blake2b", "_avx2"), ("g", "_avx2")] ==
  "vg_argon2_blake2b_avx2_g_avx2"

end VG.Test.QualifiedName
