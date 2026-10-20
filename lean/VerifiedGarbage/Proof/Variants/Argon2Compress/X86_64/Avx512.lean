module

public import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Compress
public import VerifiedGarbage.Proof.Argon2.X86_64.CompressImpl
import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx512
import VerifiedGarbage.Proof.Argon2.PermuteMany
import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Compress
import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Cols
import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Ends
import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Rows
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
# Argon2's G on x86-64 with AVX-512: the variant's code and proofs

The variant `VG.Variants.Argon2Compress.X86_64.Avx512.variant`
(`Variants/Argon2Compress/X86_64/Avx512.lean`), with the proofs its interface
asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.Argon2Compress.X86_64.Avx512

open VG VG.X86_64 VG.Proof.Argon2.X86_64

@[instance_reducible] def variant : CompressImpl where
  suffix := "_avx512"
  features := ["avx", "avx512f"]
  code := Impl.Argon2.X86_64.Avx512.compress
  correct := Avx512.compress_correct
  ct := Avx512.compress_ct
  noSp := noSp_of_allInstrs (by lit_decide)
  depth := by lit_decide
  ctl := Avx512.compress_ctl
  spSafe := by lit_decide

end VG.Proof.Variants.Argon2Compress.X86_64.Avx512
