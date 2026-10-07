import VerifiedGarbage.Impl.Weierstrass.X86.InvMemory
import VerifiedGarbage.Proof.Weierstrass.X86.Copy

/-! # Copying a multiword signed correction through a mask -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem maskCopy_ok {size : Nat} (c : Bool) : ∀ (k : Nat) {s : State} {base : Addr} {o a : Nat},
    Scr s base size → s.gpr .ecx = (if c then BitVec.allOnes 32 else 0) →
    o + 4 * k ≤ size → a + 4 * k ≤ size → (o ≤ a ∨ a + 4 * k ≤ o) →
    WP isa (.block (maskCopy k o a)) s fun u =>
      val32 u.mem base o k = (if c then val32 s.mem base a k else 0) ∧
      Keeps [.eax] s u ∧ Outside base o (4 * k) s.mem u.mem
  | 0, _, _, _, _, _, _, _, _, _ => WP.block_nil
      ⟨by cases c <;> rfl, Keeps.refl _ _, VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, s, base, o, a, hs, hc, ho, ha, sep => by
    have hn := hs.nowrap
    simp only [maskCopy, List.cons_append, List.nil_append]
    refine wp_movS (readSrc_sc hs (d := a) (by omega)) fun s₁ U₁ _ => ?_
    refine wp_logicS (.inl rfl) rfl fun s₂ U₂ => ?_
    have K₂ := U₁.keeps.trans U₂.keeps
    have hs₂ := hs.of_keeps K₂ (by decide)
    refine wp_storeS (hs₂.ea (d := o) (by omega)) (hs₂.write (d := o) (n := 4) (by omega))
      fun s₃ M₃ => ?_
    have K₃ : Keeps [.eax] s s₃ := K₂.trans (M₃.keeps _)
    have hs₃ := hs.of_keeps K₃ (by decide)
    have O₃ : Outside base o 4 s.mem s₃.mem := by
      rw [M₃.mem, U₂.mem, U₁.mem]; exact writeW32_outside _ _ _ (by omega)
    have hc₃ : s₃.gpr .ecx = (if c then BitVec.allOnes 32 else 0) := by
      rw [K₃.1 _ (by decide), hc]
    refine WP.mono (maskCopy_ok c k hs₃ hc₃ (o := o + 4) (a := a + 4)
      (by omega) (by omega) (by omega)) fun u ⟨V, K, O⟩ =>
      ⟨?_, K₃.trans K, (O₃.mono (Nat.le_refl _) (by omega)).trans (O.mono (by omega) (by omega))⟩
    rw [val32, O.w32 (by omega) (by omega), V, O₃.val32 (by omega) (by omega), M₃.mem,
      w32_write_self, U₂.gpr, U₁.gpr, U₁.other _ (by decide), hc]
    cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      BitVec.and_allOnes] <;> simp [val32, w32]

end VG.Proof.Weierstrass.X86.Inv
