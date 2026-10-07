import VerifiedGarbage.Impl.Weierstrass.X86.InvMemory
import VerifiedGarbage.Proof.Mont.X86.Chain

/-! # In-place subtraction for signed divstep products -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem subInPlace_eq (dst src n : Nat) :
    subInPlace dst src n = chainK .sub .sbb dst dst src n := rfl

theorem chainSubSelf_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {acc b : Nat} :
    ∀ k, acc + 4 * (k + 1) ≤ size → b + 4 * (k + 1) ≤ size →
    (acc + 4 * (k + 1) ≤ b ∨ b + 4 * (k + 1) ≤ acc) →
    WP isa (.block (chainK .sub .sbb acc acc b (k + 1))) s fun u =>
      Outside base acc (4 * (k + 1)) s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ val32 u.mem base acc (k + 1) + val32 s.mem base b (k + 1) =
        val32 s.mem base acc (k + 1) + 2 ^ (32 * (k + 1)) * c.toNat) ∧ Keeps [.eax] s u
  | 0, hacc, hb, _ => by
    rw [chainK_one]
    refine WP.mono (tripleSub_ok hs (.inl ⟨rfl, rfl⟩) (j := 0) (by omega) (by omega) (by omega))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ⟨O, ⟨c, hc, ?_⟩, K⟩
    simp only [val32, Nat.mul_zero, Nat.add_zero, Bool.toNat_false] at V ⊢
    exact V
  | k + 1, hacc, hb, hsb => by
    have hn := hs.nowrap
    rw [chainK_succ, ite_eq_right_of_eq_false _ _ (eq_false (Nat.add_one_ne_zero k))]
    refine WP.block_append (WP.mono (chainSubSelf_ok hs k (by omega) (by omega) (by omega))
      fun s₁ ⟨O₁, ⟨c₁, hc₁, V₁⟩, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    refine WP.mono (tripleSub_ok hs₁ (.inr ⟨rfl, hc₁⟩) (j := k + 1)
      (by omega) (by omega) (by omega)) fun u ⟨O, ⟨c, hc, V⟩, K⟩ =>
      ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (O.mono (by omega) (by omega)), ⟨c, hc, ?_⟩,
        K₁.trans K⟩
    rw [O₁.w32 (d := acc + 4 * (k + 1)) (by omega) (by omega),
      O₁.w32 (d := b + 4 * (k + 1)) (by omega) (by omega)] at V
    rw [val32_succ u.mem base acc (k + 1), val32_succ s.mem base acc (k + 1),
      val32_succ s.mem base b (k + 1), O.val32 (by omega) (by omega), pow32_succ (k + 1)]
    generalize 2 ^ (32 * (k + 1)) = P at *
    grind

end VG.Proof.Weierstrass.X86.Inv
