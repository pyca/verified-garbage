module

public import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Compress
public import VerifiedGarbage.Proof.Argon2.X86_64.CompressImpl
import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
import VerifiedGarbage.Proof.Argon2.Permutation
import VerifiedGarbage.Proof.Argon2.X86_64.Compress
import VerifiedGarbage.Proof.Argon2.X86_64.Finish
import VerifiedGarbage.Proof.Argon2.X86_64.Mix
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Sse

/-!
# Argon2's G on x86-64 with AVX2: the variant's code and proofs

The variant `VG.Variants.Argon2Compress.X86_64.Avx2.variant`
(`Variants/Argon2Compress/X86_64/Avx2.lean`), with the proofs its interface
asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.Argon2Compress.X86_64.Avx2

open VG VG.X86_64 VG.Proof.Argon2.X86_64

@[instance_reducible] def variant : CompressImpl where
  suffix := "_avx2"
  features := ["avx", "avx2"]
  code := Impl.Argon2.X86_64.Avx2.compress
  correct := Avx2.compress_correct
  ct := Avx2.compress_ct
  noSp := noSp_of_allInstrs (by lit_decide)
  depth := by lit_decide
  ctl := Avx2.compress_ctl
  spSafe := by lit_decide

end VG.Proof.Variants.Argon2Compress.X86_64.Avx2
