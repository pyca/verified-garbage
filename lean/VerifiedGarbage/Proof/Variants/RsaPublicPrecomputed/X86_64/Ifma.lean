module

public import VerifiedGarbage.Proof.Framework.X86_64.InstrBits
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedBackend
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubCT
public import VerifiedGarbage.Impl.Rsa.X86_64.PubIfma
public import VerifiedGarbage.Proof.Bignum.Amm52
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTChecked
public import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubLit
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Bignum.X86_64.Ifma.PubCode`, which only this module used -/

section

/-! # `vg_rsa_public_precomputed_checked_ifma`: correctness -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma.Pub
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Checked
open VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Bignum.X86_64.FoldedPublic
open VG.Proof.MlKem.X86_64

/-- `vg_rsa_public_precomputed_checked_ifma`: the code runs only for a valid `e`. -/
theorem checked_correct (M : Mont)
    (hmx : (seqs (phases M)).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : pdContract.pre s) :
    ∃ tr t, Exec isa (PubIfma.checked M.mm) s tr t ∧ abiPreserved s t ∧ pdChkContract.post s t := by
  refine guarded_correct (fun s h hv => codeWith_correct (PubIfma.rest M.mm) (fun hp => rest_ok M hp hmx) s h
      (by simpa only [eValid, eBytes] using hv))
    (fun _ h => pdGeom h) (fun s t hs h => (pdPre_same hs).symm ▸ h) ?_ ?_ s h
  · intro s t s' _ hs hv hp nB hl hpre
    simp only [pdContract, stackArg_same hs, hs.rdi, hs.rsi, hs.rdx, hs.rcx, hs.r8, hs.r9, hs.mem] at hp
    simp only [eValid, eBytes] at hv
    simp only [Spec.Rsa.publicOpChecked, hv, ↓reduceIte]
    exact hp nB hl hpre
  · intro s s' h hv hb hax nB _ _
    simp only [eValid, eBytes] at hv
    simp only [Spec.Rsa.publicOpChecked, hv, Bool.false_eq_true, ite_false, Spec.Rsa.written, hax]
    exact ⟨rfl, hb⟩

end VG.Proof.Bignum.X86_64.Ifma.Pub

end

end


/-!
# Precomputed RSA public operation: with AVX512_IFMA: the variant's code and proofs

The variant `VG.Variants.RsaPublicPrecomputed.X86_64.Ifma.variant`
(`Variants/RsaPublicPrecomputed/X86_64/Ifma.lean`), with the proofs its
interface asks for: for `e = 65537` and 2048-, 3072- and 4096-bit moduli,
the vector code; otherwise the ADX code's.
-/

@[expose] public section

namespace VG.Proof.Variants.RsaPublicPrecomputed.X86_64.Ifma

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- The tests of the code's instructions, in one walk. -/
theorem checked_bits : (Impl.Rsa.X86_64.PubIfma.checked Mont.adxSquare.mm).allInstrs (hasBits (bMx + bSp + bNs)) = true ∧
    (Impl.Rsa.X86_64.PubIfma.checked Mont.adxSquare.mm).depth = 0 ∧
    (Impl.Rsa.X86_64.PubIfma.checked Mont.adxSquare.mm).x86_64Depth ≤ 0 ∧
    (UpperLock.inames (Impl.Rsa.X86_64.PubIfma.checked Mont.adxSquare.mm)).isEmpty = true := by
  lit_decide

def variant : PublicImpl where
  name := "vg_rsa_public_precomputed_checked" ++ "_ifma"
  code := Impl.Rsa.X86_64.PubIfma.checked Mont.adxSquare.mm
  ok := Ifma.Pub.checked_correct _ (by decide +kernel)
  ct := Ifma.Pub.checked_ct _ FoldedPublic.adx_final_ct
  nosp := noSp_of (Code.noRsp_of_bits rfl checked_bits.1)
  depth := checked_bits.2.1
  spSafe := Code.spSafe_of_bits rfl checked_bits.1
  level := .evex
  side := X86_64.Scrub.calleeSide_evex checked_bits.2.2.1 (Code.noMx_of_bits rfl checked_bits.1) checked_bits.2.2.2
  up := fun h => by cases h
  suffix := "_ifma"
  features := ["avx", "avx512f", "avx512ifma", "avx512vl", "bmi2", "adx"]

end VG.Proof.Variants.RsaPublicPrecomputed.X86_64.Ifma
