module

public import VerifiedGarbage.Proof.AesGcm.X86.Callee
public import VerifiedGarbage.Proof.Gcm.X86.Pclmul.Ghash
public import VerifiedGarbage.Proof.Gcm.X86.Law
import VerifiedGarbage.Proof.Gcm.X86.Lit
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.VariantProof
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM on x86: the implementations of `vg_ghash`

Untrusted: everything here is checked by Lean. The `GhashImpl`s of
`vg_ghash` and `vg_ghash_pclmul`, from their proofs, apart from
`Callee.lean`: only the variants need them, and their proofs import the
algebra of `Proof/Gcm/Poly.lean`, which the rest of the AES-GCM proofs then
need not import.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86

open VG VG.X86

variable {N : Nat}

namespace GhashImpl

/-- `vg_ghash`, in the baseline ISA. -/
def scalar : GhashImpl where
  fn := ⟨"vg_ghash", Impl.Gcm.X86.ghash⟩
  stack := by lit_decide
  ok := Proof.Gcm.X86.ghash_correct
  ct := Proof.Gcm.X86.ghash_ct
  nosp := NoSp.of_all (by lit_decide)
  spSafe := Code.all_of_spTest (by lit_decide)
  scrub := by lit_decide
  suffix := ""
  features := []

/-- `vg_ghash_pclmul`. -/
def pclmul : GhashImpl where
  fn := ⟨"vg_ghash_pclmul", Impl.Gcm.X86.Pclmul.ghash⟩
  stack := by lit_decide
  ok := Proof.Gcm.X86.Pclmul.ghash_correct
  ct := Proof.Gcm.X86.Pclmul.ghash_ct
  nosp := NoSp.of_all (by lit_decide)
  spSafe := Code.all_of_spTest (by lit_decide)
  scrub := by lit_decide
  suffix := "_pclmul"
  features := ["pclmulqdq", "ssse3"]

end GhashImpl

/-- The implementation of `vg_ghash` named `n`. -/
def GhashName.impl : GhashName → GhashImpl
  | .scalar => .scalar
  | .pclmul => .pclmul

/-- The implementations a variant calls. -/
def GcmVariant.impl (v : GcmVariant) : GcmImpl := ⟨v.ctr, v.gh.impl⟩

end VG.Proof.AesGcm.X86
