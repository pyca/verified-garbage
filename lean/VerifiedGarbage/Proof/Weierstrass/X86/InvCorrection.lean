import VerifiedGarbage.Proof.Weierstrass.X86.InvSignMask
import VerifiedGarbage.Proof.Weierstrass.X86.InvSub

/-! # Correcting an unsigned row for a negative coefficient -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem correction_ok {s : State} {base : Addr} {size coefficient acc src tmp k : Nat}
    (hs : Scr s base size) (hc : coefficient + 4 ≤ size) (ha : acc + 4 * (k + 2) ≤ size)
    (hb : src + 4 * (k + 1) ≤ size) (ht : tmp + 4 * (k + 1) ≤ size)
    (st : tmp + 4 * (k + 1) ≤ acc ∨ acc + 4 * (k + 2) ≤ tmp)
    (sb : tmp ≤ src ∨ src + 4 * (k + 1) ≤ tmp) :
    WP isa (.block (correction coefficient acc src tmp (k + 2))) s fun u =>
      Unch base [(acc, 4 * (k + 2)), (tmp, 4 * (k + 1))] s.mem u.mem ∧ Keeps clob s u ∧
      ∃ c : Bool, val32 u.mem base acc (k + 2) + 2 ^ 32 *
          (if 2 ^ 31 ≤ w32 s.mem base coefficient then val32 s.mem base src (k + 1) else 0) =
        val32 s.mem base acc (k + 2) + 2 ^ (32 * (k + 2)) * c.toNat := by
  have hn := hs.nowrap
  unfold correction
  rw [show k + 2 - 1 = k + 1 by omega]
  refine WP.block_append (WP.block_append (WP.mono (maskOf_ok hs hc) fun s₁ ⟨C₁, K₁, M₁⟩ => ?_))
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (maskCopy_ok (decide (2 ^ 31 ≤ w32 s.mem base coefficient)) (k + 1) hs₁
    (by simpa using C₁) ht hb sb) fun s₂ ⟨V₂, K₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  simp only [M₁, decide_eq_true_eq] at V₂
  rw [subInPlace_eq]
  refine WP.mono (chainSubSelf_ok hs₂ k (acc := acc + 4) (b := tmp)
    (by omega) ht (by omega)) fun u ⟨O₃, ⟨c, _, V₃⟩, K₃⟩ => ?_
  refine ⟨?_, ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide)), c, ?_⟩
  · intro x hx
    have xa := hx (acc, 4 * (k + 2)) (by simp)
    have xt := hx (tmp, 4 * (k + 1)) (by simp)
    rw [O₃ x (by omega), O₂ x xt, M₁]
  · rw [V₂, O₂.val32 (d := acc + 4) (k := k + 1) (by omega) (by omega), M₁] at V₃
    change w32 u.mem base acc + 2 ^ 32 * val32 u.mem base (acc + 4) (k + 1) + _ =
      w32 s.mem base acc + 2 ^ 32 * val32 s.mem base (acc + 4) (k + 1) + _
    rw [O₃.w32 (by omega) (by omega), O₂.w32 (by omega) (by omega), M₁,
      show k + 2 = (k + 1) + 1 by omega, pow32_succ]
    have := congrArg (fun x => 2 ^ 32 * x) V₃
    simp only [Nat.mul_add, ← Nat.mul_assoc] at this ⊢
    omega

end VG.Proof.Weierstrass.X86.Inv
