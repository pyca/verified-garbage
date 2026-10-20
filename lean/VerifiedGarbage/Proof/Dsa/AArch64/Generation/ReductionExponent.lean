module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Rsa.Ranges
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Reduce
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateReduction
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Double
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Generation.PReduction

/-! # Candidate reduction also produces the generator exponent -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.Bignum VG.Proof.MlKem.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.Rsa VG.Proof.Dsa.Generation

theorem reduceExponent_ok {s : State} {B : Addr} {Z w x q : Nat}
    (h : Ws s B Z w) (hx : wv s.mem B (slot w 0) w = x)
    (hq : wv s.mem B (slot w 2) w = 2 * q) (hqpos : 0 < q) :
    WP isa (.seq Impl.Dsa.AArch64.Generation.reduceCandidate
      (Impl.Dsa.AArch64.Generation.doubleArray 0)) s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w 5) w = x + 1 - x % (2 * q) ∧
      wv t.mem B (slot w 0) w = (x + 1 - x % (2 * q) - 1) / q ∧
      Frm B [ar w 4, ar w 0, ar w 1, ar w 3, ar w 5] s.mem t.mem ∧
      Keep mmRegs s t := by
  have hxlt : x < 2 ^ (64 * w) := hx ▸ wv_lt s.mem B (slot w 0) w
  have he : 2 * (x / (2 * q)) ≤ x := by
    calc
      2 * (x / (2 * q)) ≤ q * (2 * (x / (2 * q))) := Nat.le_mul_of_pos_left _ hqpos
      _ = 2 * q * (x / (2 * q)) := by ac_rfl
      _ ≤ x := Nat.mul_div_le x (2 * q)
  refine WP.seq (WP.mono (reduceCandidate_ok h hx hq hqpos) fun u ⟨hu, hp, hquot, hf, hk⟩ => ?_)
  refine WP.mono (doubleArray_ok hu (by decide : 0 < 16) (by rw [hquot]; omega))
    fun t ⟨ht, ho, kt⟩ => ?_
  have ft : Frm B [ar w 0] u.mem t.mem :=
    Frm.of_outside (ho.mono (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp [ar])
  have wt := hu.congr ft (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) kt (by decide)
  refine ⟨wt, ?_, ?_, ?_, (hk.trans kt).mono (by decide)⟩
  · rw [ft.wv_eq (by
      simp only [List.mem_singleton]; rintro r rfl
      simp only [slot, hdrBytes]; omega) (by have := h.sl (by decide : 5 < 16); have := h.scr.nowrap; omega), hp]
  · rw [ht, hquot, pReduction_generatorExponent x hqpos]
  · exact hf.trans (ft.mono (by simp))

end VG.Proof.Dsa.AArch64.Generation
