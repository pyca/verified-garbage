module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeSetup

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusFrame
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega

/-! Convert a sampled witness to Montgomery form using the shared arithmetic. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

def witnessMontRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))]

theorem witnessMont_ok (M : Mont) {s : State} {B : Addr} {Z w N b : Nat}
    (h : ModulusReady s B Z w N) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hodd : N % 2 = 1) (hN1 : 1 < N) (hx : wv s.mem B (slot w aX) w = b) :
    WP isa (M.mm aXm aX aR2) s fun t =>
      ModulusReady t B Z w N ∧ wv t.mem B (slot w aXm) w = b * 2 ^ (64 * w) % N ∧
      Frm B (witnessMontRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw := h.ws.w2
  have hn := h.ws.scr.nowrap
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  refine WP.mono (M.mm_ok h.ws.good.1 h.ws.good.2 h.ws.w1 (by omega)
    (o := aXm) (a := aX) (b := aR2) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) h.inverse
    (by rw [h.r2, h.modulus]; exact Nat.mod_lt _ (by omega))) fun t ⟨_, hlt, hy, ha, hk⟩ => ?_
  rw [h.modulus] at hlt hy
  rw [hx, h.r2] at hy
  have hXm : wv t.mem B (slot w aXm) w = b * 2 ^ (64 * w) % N := by
    rw [← Nat.mod_eq_of_lt hlt]
    refine VG.Proof.Bignum.mont_cancel hR ?_
    rw [hy, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have hf : Frm B (witnessMontRanges w) s.mem t.mem := Frm.of_arrays ha (by simp [witnessMontRanges])
  refine ⟨h.of_frm hEZ hf ?_ hk (by decide) ?_ ?_ ?_, hXm, hf, hk⟩
  · intro r hr
    simp only [witnessMontRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact KMut.ofSlot w _ _
  · intro a ha r hr
    simp only [modulusArrays, List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [witnessMontRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl <;>
      simp only [slot, hdrBytes, aN, aOne, aR2, aR1, aRm1, aAcc, aTmp, aXm] <;> omega_arith
  · intro r hr
    simp only [witnessMontRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      left <;> simp only [slot, hdrBytes, aAcc, aTmp, aXm, sMinv] <;> omega_arith
  · intro r hr
    simp only [witnessMontRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      right <;> simp only [slot, hdrBytes, aAcc, aTmp, aXm, aE] <;> omega_arith

end VG.Proof.Dsa.AArch64.Generation
