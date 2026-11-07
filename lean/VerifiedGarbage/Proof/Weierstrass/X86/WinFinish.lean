module

public import VerifiedGarbage.Proof.Weierstrass.X86.WinQuad
public import VerifiedGarbage.TCB.X86.State
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Weierstrass.CombLay

/-! ## `WinFlags` -/

@[expose] public section

section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

/-- The `or`s of `nonzero`. -/
theorem winOrs_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat} :
    ∀ k, a + 4 * (k + 1) ≤ size →
    WP isa (.block ((List.range k).map fun j => .alu .or .edx (.mem (sc (a + 4 * (j + 1)))))) s fun s' =>
      (s'.gpr .edx = 0 ↔ s.gpr .edx = 0 ∧ ∀ j < k, w32 s.mem base (a + 4 * (j + 1)) = 0) ∧
      Keeps [.edx] s s' ∧ s'.mem = s.mem
  | 0, _ => WP.block_nil ⟨⟨fun h => ⟨h, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩, fun h => h.1⟩,
      Keeps.refl _ _, rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append (WP.mono (winOrs_ok hs k (by omega_arith)) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    have hs₁ := hs.of_keeps k₁ (by decide)
    refine wp_orS (readSrc_sc hs₁ (d := a + 4 * (k + 1)) (by omega_arith)) fun s₂ u₂ => WP.block_nil
      ⟨?_, k₁.trans u₂.keeps, by rw [u₂.mem, m₁]⟩
    have hor : ∀ x y : BitVec 32, x ||| y = 0 ↔ x = 0 ∧ y = 0 := fun _ _ => BitVec.or_eq_zero_iff
    rw [u₂.gpr, hor, e₁, m₁]
    have hw : (s.mem.readW (off base (a + 4 * (k + 1))) 32 = 0) ↔ w32 s.mem base (a + 4 * (k + 1)) = 0 :=
      ⟨fun h => by simp [w32, h], fun h => BitVec.eq_of_toNat_eq h⟩
    rw [hw]
    constructor
    · intro ⟨⟨h₀, h⟩, hw⟩
      refine ⟨h₀, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j k with hj' | hj'
      · exact h j hj'
      · obtain rfl : j = k := by omega_arith
        exact hw
    · intro ⟨h₀, h⟩
      exact ⟨⟨h₀, fun j hj => h j (by omega_arith)⟩, h k (by omega_arith)⟩

end VG.Proof.Weierstrass.X86

end

/-! ## `WinFinish` -/

