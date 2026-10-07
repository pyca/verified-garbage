import VerifiedGarbage.Proof.Weierstrass.X86.InvRedWord
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedSumMath
import VerifiedGarbage.Proof.Weierstrass.X86.InvSignMask
import VerifiedGarbage.Proof.Weierstrass.X86.InvLoop

/-! # The signed numerator of a divstep coefficient reduction -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem redSum_ok {s : State} {base : Addr} {size acc modulus tmp n : Nat} (minv : BitVec 32)
    (hs : Scr s base size) (ha : acc + 4 * (n + 2) ≤ size) (hm : modulus + 4 * n ≤ size)
    (ht : tmp + 4 ≤ size)
    (sta : tmp + 4 ≤ acc ∨ acc + 4 * (n + 2) ≤ tmp)
    (sam : acc + 4 * (n + 2) ≤ modulus ∨ modulus + 4 * n ≤ acc)
    (stm : tmp + 4 ≤ modulus ∨ modulus + 4 * n ≤ tmp) :
    WP isa (.block (redSum acc modulus tmp n minv)) s fun z =>
      Unch base [(acc, 4 * (n + 2)), (tmp, 4)] s.mem z.mem ∧ Keeps wordClob s z ∧
      val32 z.mem base acc (n + 2) =
        (val32 s.mem base acc (n + 1) +
          (w32 s.mem base acc * minv.toNat % 2 ^ 32) * val32 s.mem base modulus n +
          2 ^ (32 * (n + 1)) *
            (if 2 ^ 31 ≤ w32 s.mem base (acc + 4 * n) then 2 ^ 32 - 1 else 0)) %
          2 ^ (32 * (n + 2)) := by
  have hn := hs.nowrap
  unfold redSum
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append (WP.block_append
    (WP.mono (maskOf_ok hs (by omega)) fun s₁ ⟨C₁, K₁, M₁⟩ => ?_)))))
  refine wp_movS rfl fun s₂ U₂ _ => WP.block_nil ?_
  have K₂ : Keeps wordClob s s₂ := (K₁.mono (by decide)).trans (U₂.keeps.mono (by decide))
  have M₂ : s₂.mem = s.mem := U₂.mem.trans M₁
  have hs₂ := hs.of_keeps K₂ (by decide)
  refine WP.mono (zeros_ok hs₂ (acc := acc + 4 * (n + 1)) (k := 1) (by omega))
    fun s₃ ⟨O₃, V₃, K₃⟩ => ?_
  have V₃' : val32 s₃.mem base acc (n + 2) = val32 s.mem base acc (n + 1) := by
    simp only [val32, Nat.mul_zero, Nat.add_zero] at V₃
    rw [val32_succ, O₃.val32 (by omega) (by omega), V₃, M₂, Nat.mul_zero, Nat.add_zero]
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  refine WP.mono (quotientWord_ok minv hs₃ (by omega) ht) fun s₄ ⟨Q₄, K₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keeps K₄ (by decide)
  rw [O₃.w32 (by omega) (by omega), M₂] at Q₄
  have V₄ : val32 s₄.mem base acc (n + 2) = val32 s.mem base acc (n + 1) := by
    rw [O₄.val32 (by omega) (by omega), V₃']
  have P₄ : val32 s₄.mem base modulus n = val32 s.mem base modulus n := by
    rw [O₄.val32 (by omega) (by omega), O₃.val32 (by omega) (by omega), M₂]
  refine WP.mono (rowAdd_ok hs₄ ht ha hm (by omega)
    (row_bound (by rw [V₄]; exact val32_lt _ _ _ _))) fun s₅ ⟨O₅, V₅, K₅⟩ => ?_
  rw [V₄, Q₄, P₄] at V₅
  have hs₅ := hs₄.of_keeps K₅ (by decide)
  refine WP.mono (addSignWord_ok hs₅ (dst := acc + 4 * (n + 1)) (by omega))
    fun z ⟨V₆, K₆, O₆⟩ => ⟨?_, ?_, ?_⟩
  · intro x hx
    have hacc := hx (acc, 4 * (n + 2)) (by simp)
    have htmp := hx (tmp, 4) (by simp)
    rw [O₆ x (by omega), O₅ x hacc, O₄ x htmp, O₃ x (by omega), M₂]
  · exact (((K₂.trans (K₃.mono (by decide))).trans (K₄.mono (by decide))).trans
      (K₅.mono (by decide))).trans (K₆.mono (by decide))
  · have S : (s₅.gpr .esi).toNat =
        if 2 ^ 31 ≤ w32 s.mem base (acc + 4 * n) then 2 ^ 32 - 1 else 0 := by
      rw [K₅.1 _ (by decide), K₄.1 _ (by decide), K₃.1 _ (by decide), U₂.gpr, C₁]
      split <;> rfl
    rw [val32_succ, O₆.val32 (by omega) (by omega), V₆, S]
    have E := add_top_mod (top := w32 s₅.mem base (acc + 4 * (n + 1)))
      (sign := if 2 ^ 31 ≤ w32 s.mem base (acc + 4 * n) then 2 ^ 32 - 1 else 0)
      (Nat.two_pow_pos (32 * (n + 1))) (val32_lt s₅.mem base acc (n + 1))
    rw [E, ← val32_succ, Nat.mul_comm (2 ^ (32 * (n + 1))) (2 ^ 32), ← pow32_succ, V₅]

end VG.Proof.Weierstrass.X86.Inv
