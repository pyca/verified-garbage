module

public import VerifiedGarbage.Proof.Argon2.X86_64.Compress
public import VerifiedGarbage.Proof.Argon2.X86_64.CompressImpl
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Argon2.Permutation
import VerifiedGarbage.Proof.Argon2.X86_64.Finish
import VerifiedGarbage.Proof.Argon2.X86_64.Mix
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked

/-!
# Argon2's G on baseline x86-64: the variant's code and proofs

The variant `VG.Variants.Argon2Compress.X86_64.Scalar.variant`
(`Variants/Argon2Compress/X86_64/Scalar.lean`), with the proofs its interface
asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.Argon2Compress.X86_64.Scalar

open VG VG.X86_64 VG.Proof.Argon2.X86_64

@[instance_reducible] def variant : CompressImpl where
  suffix := ""
  features := []
  code := Impl.Argon2.X86_64.compress
  correct := compress_correct
  ct := compress_ct
  noSp := noSp_of_allInstrs (by lit_decide)
  depth := by lit_decide
  ctl := ctlOk_of_allInstrs (by lit_decide)
  spSafe := by lit_decide

end VG.Proof.Variants.Argon2Compress.X86_64.Scalar
