import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseWord
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.Spec.MlDsa

/-- A small accepted signed representative has exactly the field norm tested
by the canonical signing specification, even when reduce32 is not centered. -/
theorem reduced_norm_iff (x : Int) (B : Nat)
    (hl : -4202495≤x) (hh : x≤4210685) (hB : B≤524288) :
    normZq (ofInt x)<B ↔ -(B:Int)<x ∧ x<(B:Int) := by
  rw [VG.Proof.MlDsa.Round.normZq_lt]
  have hv := VG.Proof.MlDsa.KeyGen.ofInt_val x
  have hr := (ofInt x).isLt
  change (ofInt x).val<8380417 at hr
  change (ofInt x).val<B ∨ 8380417-(ofInt x).val<B ↔ _
  omega

theorem reduce32_norm_iff (x : Int) (B : Nat)
    (hl : -2*8380417<x) (hh : x<3*8380417) (hB : B≤524288) :
    normZq (ofInt x)<B ↔ -(B:Int)<reduce32 x ∧ reduce32 x<(B:Int) := by
  have he : ofInt (reduce32 x)=ofInt x := by
    apply Fin.ext
    have h1 := VG.Proof.MlDsa.KeyGen.ofInt_val (reduce32 x)
    have h2 := VG.Proof.MlDsa.KeyGen.ofInt_val x
    have h3 := reduce32_mod x
    omega
  rw [← he]
  exact reduced_norm_iff _ _ (reduce32_bounds hl hh).1 (reduce32_bounds hl hh).2 hB

end VG.Proof.MlDsa.AArch64.Optimized.Response
