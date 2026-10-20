module
public import VerifiedGarbage.Impl.Rsa.X86_64.CheckKeyCore
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyCtx

import VerifiedGarbage.Proof.Rsa.X86_64.KeySteps
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks

/-!
# Full-exponent products and their bounded quotients

Zero-extend `e d` to both accumulator slots, including for padded factors.
The quotient bound is needed only when `d < n` and `p q = n` hold.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask)

theorem mulEWideK {s t : State} {B : Addr} {Z w N : Nat} {minv : BitVec 64}
    (h : KCtx s t B Z w minv N) :
    WP isa (seqs mulEWide) t fun t' => KCtx s t' B Z w minv N ∧
      wv t'.mem B (slot w aAcc) (2 * w + 4) =
        (word s.mem B (8 * sEv)).toNat * wv t.mem B (slot w aX) w ∧
      Arrays B w [aAcc, aTmp] t.mem t'.mem := by
  have hn := h.good.scr.nowrap
  have hw := h.w2
  have hZ := h.hZ
  have es : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot hdrBytes aAcc aTmp; omega
  unfold mulEWide
  refine wsa (by simp) (by simp [mulE]) (WP.mono
    (zeroArr_ok h.good hZ h.w1 (by omega) (show aTmp < 8 by decide)) fun t₁ ⟨hz, ho, hk⟩ => ?_)
  have ha : Arrays B w [aTmp] t.mem t₁.mem := Arrays.of_outside (by simp) ho (Nat.le_refl _) (Nat.le_refl _)
  have h₁ := h.arr ha (by decide) (by decide) (by decide) hk
  refine WP.mono (mulEK h₁) fun t₂ ⟨h₂, hv, ha₂⟩ => ⟨h₂, ?_, ?_⟩
  · rw [show 2 * w + 4 = (w + 2) + (w + 2) by omega, wv_add, es]
    have hz₂ : wv t₂.mem B (slot w aTmp) (w + 2) = 0 := by
      rw [ha₂.wv_eq (fun j hj => by
        simp only [List.mem_singleton] at hj
        subst j
        exact Or.inr (Nat.le_of_eq es)) (by unfold slot hdrBytes aTmp; omega), hz]
    rw [hz₂, Nat.mul_zero, Nat.add_zero, hv, Arrays.wv_other ha (by decide) (by decide) hZ hn]
  · exact (ha.mono (by simp)).trans (ha₂.mono (by simp))

theorem topD_ok {t : State} {B : Addr} {Z w sl L : Nat} {minv : BitVec 64}
    (hg : Good t B Z w minv) (hZ : slot w 8 ≤ Z) (hsl : sl < 32)
    (hL : word t.mem B (8 * sl) = BitVec.ofNat 64 L) (hL2 : L < 2 ^ 32) :
    WP isa (.block (topD sl)) t fun t' => t'.gpr .r13 = BitVec.ofNat 64 ((L + 7) / 8 + 1) ∧
      t'.mem = t.mem ∧ Keep [.r13] t t' := by
  refine WP.mono (WP.keep [.r13] (Q := fun t' => t'.gpr .r13 = BitVec.ofNat 64 ((L + 7) / 8 + 1) ∧ t'.mem = t.mem)
    (by
      xrun [topD, State.ea, hdr, hg.rdi, hdrOff,
        hg.scr.ld (d := 8 * sl) (by have := hdr_lt_slot w 8 hsl; omega), hL, shr3_w L hL2]
      rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]) rfl)
    fun _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩

/-- A bound expressed only through the other factor's public byte length. -/
theorem fullExp_bound {e d x y L : Nat} (he : e < 2 ^ 33) (hx : 2 ≤ x)
    (hd : d < x * y) (hy : y < 2 ^ (64 * ((L + 7) / 8))) :
    e * d < 2 ^ (64 * ((L + 7) / 8 + 1)) * (x - 1) := by
  have hx' : x ≤ 2 * (x - 1) := by omega
  have hxy : x * y ≤ 2 * (x - 1) * y := Nat.mul_le_mul_right y hx'
  have hed : e * d ≤ e * (2 * (x - 1) * y) := Nat.mul_le_mul_left e (by omega)
  have hey : e * y < 2 ^ 33 * 2 ^ (64 * ((L + 7) / 8)) := Nat.mul_lt_mul_of_lt_of_lt he hy
  have hsmall : 2 * (2 ^ 33 * 2 ^ (64 * ((L + 7) / 8))) ≤ 2 ^ (64 * ((L + 7) / 8 + 1)) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_right (2 ^ (64 * ((L + 7) / 8))) (show 2 * 2 ^ 33 ≤ (2 : Nat) ^ 64 by decide)
  have hpos : 0 < x - 1 := by omega
  calc e * d ≤ (2 * (e * y)) * (x - 1) := by simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hed
    _ < (2 * (2 ^ 33 * 2 ^ (64 * ((L + 7) / 8)))) * (x - 1) :=
      Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hey (by decide)) hpos
    _ ≤ _ := Nat.mul_le_mul_right _ hsmall

end VG.Proof.Rsa.X86_64.Key
