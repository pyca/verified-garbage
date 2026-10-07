import VerifiedGarbage.Proof.Weierstrass.X86.InvAdd
import VerifiedGarbage.Proof.Weierstrass.X86.InvSignMask
import VerifiedGarbage.Proof.Mont.X86.Ops

/-! # Adding the modulus under the sign mask -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem addInPlace_eq (dst src n : Nat) :
    addInPlace dst src n = chainK .add .adc dst dst src n := rfl

theorem addIfNeg_ok {s : State} {base : Addr} {size acc modulus tmp n : Nat}
    (hs : Scr s base size) (ha : acc + 4 * (n + 1) ≤ size) (hm : modulus + 4 * n ≤ size)
    (ht : tmp + 4 * (n + 1) ≤ size)
    (sta : tmp + 4 * (n + 1) ≤ acc ∨ acc + 4 * (n + 1) ≤ tmp)
    (stm : tmp + 4 * (n + 1) ≤ modulus ∨ modulus + 4 * n ≤ tmp) :
    WP isa (.block (addIfNeg acc modulus tmp n)) s fun u =>
      Unch base [(acc, 4 * (n + 1)), (tmp, 4 * (n + 1))] s.mem u.mem ∧ Keeps [.eax, .ecx] s u ∧
      val32 u.mem base acc (n + 1) =
        (val32 s.mem base acc (n + 1) +
          if 2 ^ 31 ≤ w32 s.mem base (acc + 4 * n) then val32 s.mem base modulus n else 0) %
          2 ^ (32 * (n + 1)) := by
  have hn := hs.nowrap
  unfold addIfNeg
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono
    (maskOf_ok hs (by omega)) fun s₁ ⟨C₁, K₁, M₁⟩ => ?_)))
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (maskCopy_ok (decide (2 ^ 31 ≤ w32 s.mem base (acc + 4 * n))) n hs₁
    (by simpa using C₁) (by omega) hm (by omega)) fun s₂ ⟨V₂, K₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  simp only [M₁, decide_eq_true_eq] at V₂
  refine WP.mono (zeros_ok hs₂ (acc := tmp + 4 * n) (k := 1) (by omega)) fun s₃ ⟨O₃, V₃, K₃⟩ => ?_
  have Vtmp : val32 s₃.mem base tmp (n + 1) =
      if 2 ^ 31 ≤ w32 s.mem base (acc + 4 * n) then val32 s.mem base modulus n else 0 := by
    simp only [val32, Nat.mul_zero, Nat.add_zero] at V₃
    rw [val32_succ, O₃.val32 (by omega) (by omega), V₃, V₂, Nat.mul_zero, Nat.add_zero]
  have VAcc : val32 s₃.mem base acc (n + 1) = val32 s.mem base acc (n + 1) := by
    rw [O₃.val32 (by omega) (by omega), O₂.val32 (by omega) (by omega), M₁]
  rw [addInPlace_eq]
  refine WP.mono (chainAddSelf_ok (hs₂.of_keeps K₃ (by decide)) n ha ht (by omega))
    fun u ⟨O₄, ⟨c, _, V₄⟩, K₄⟩ => ⟨?_, ?_, ?_⟩
  · intro x hx
    have hacc := hx (acc, 4 * (n + 1)) (by simp)
    have htmp := hx (tmp, 4 * (n + 1)) (by simp)
    rw [O₄ x hacc, O₃ x (by omega), O₂ x (by omega), M₁]
  · exact ((K₁.trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
      (K₄.mono (by decide))
  · rw [Vtmp, VAcc] at V₄
    have E := congrArg (fun x => x % 2 ^ (32 * (n + 1))) V₄
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt _ _ _ _)] at E
    exact E

end VG.Proof.Weierstrass.X86.Inv
