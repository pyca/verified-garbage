import VerifiedGarbage.Proof.Blowfish.AArch64.Lookup
import VerifiedGarbage.Proof.Blowfish.AArch64.Transpose

/-!
# Byte planes in and out, and the accumulation of F

`planes_run`: `planes L` leaves in `idxReg j` byte `3 - j` of each word of
`L`. `words_run`: `words` turns the byte planes in `outReg` into words.
`combine_run`: `combine j` accumulates them into `fReg`.
-/

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.AArch64.Tbl (VOnly)

/-- The registers `planes` writes. -/
def planesRegs : List VReg := [.v0, .v1, .v20, .v21, .v16, .v17, .v18, .v19]

theorem four_regs (v : VReg → BitVec 128) (L : Nat → VReg) {k : Nat} (hk : k < 4) :
    four (v (L 0)) (v (L 1)) (v (L 2)) (v (L 3)) k = v (L k) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem planes_run (s : State) (L : Nat → VReg) (hL : ∀ k < 4, L k ∉ planesRegs) :
    ∃ s', runBlock isa (planes L) s = some s' ∧
      (∀ j < 4, ∀ n < 16, vbyte (s'.v (idxReg j)) n = vbyte (s.v (L (n / 4))) (4 * (n % 4) + (3 - j))) ∧
      VOnly planesRegs s s' := by
  have h0 := hL 0 (by decide); have h1 := hL 1 (by decide)
  have h2 := hL 2 (by decide); have h3 := hL 3 (by decide)
  simp only [planesRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h0 h1 h2 h3
  let p (o : Nat) (t : State) (d n m : VReg) := t.setV d (VPermOp.eval (uzp o) .b16 (t.v n) (t.v m))
  let s₁ := p 0 s .v0 (L 0) (L 1)
  let s₂ := p 1 s₁ .v1 (L 0) (L 1)
  let s₃ := p 0 s₂ .v20 (L 2) (L 3)
  let s₄ := p 1 s₃ .v21 (L 2) (L 3)
  let s₅ := p 0 s₄ .v19 .v0 .v20
  let s₆ := p 1 s₅ .v17 .v0 .v20
  let s₇ := p 0 s₆ .v18 .v1 .v21
  let s₈ := p 1 s₇ .v16 .v1 .v21
  refine ⟨s₈, ?_, ?_, ?_⟩
  · have e₁ : exec (vperm .uzp1 .b16 .v0 (L 0) (L 1)) s = some s₁ := rfl
    have e₂ : exec (vperm .uzp2 .b16 .v1 (L 0) (L 1)) s₁ = some s₂ := rfl
    have e₃ : exec (vperm .uzp1 .b16 (outReg 0) (L 2) (L 3)) s₂ = some s₃ := rfl
    have e₄ : exec (vperm .uzp2 .b16 (outReg 1) (L 2) (L 3)) s₃ = some s₄ := rfl
    have e₅ : exec (vperm .uzp1 .b16 (idxReg 3) .v0 (outReg 0)) s₄ = some s₅ := rfl
    have e₆ : exec (vperm .uzp2 .b16 (idxReg 1) .v0 (outReg 0)) s₅ = some s₆ := rfl
    have e₇ : exec (vperm .uzp1 .b16 (idxReg 2) .v1 (outReg 1)) s₆ = some s₇ := rfl
    have e₈ : exec (vperm .uzp2 .b16 (idxReg 0) .v1 (outReg 1)) s₇ = some s₈ := rfl
    rw [planes, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_cons,
      e₆, runStep_some, runBlock_cons, e₇, runStep_some, runBlock_cons, e₈, runStep_some, runBlock_nil]
  · have hne : ∀ k < 4, L k ≠ .v0 ∧ L k ≠ .v1 ∧ L k ≠ .v20 ∧ L k ≠ .v21 := fun k hk => by
      have := hL k hk
      simp only [planesRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at this
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
    have r1 : s₄.v .v0 = VPermOp.eval (uzp 0) .b16 (s.v (L 0)) (s.v (L 1)) ∧
        s₄.v .v1 = VPermOp.eval (uzp 1) .b16 (s.v (L 0)) (s.v (L 1)) ∧
        s₄.v .v20 = VPermOp.eval (uzp 0) .b16 (s.v (L 2)) (s.v (L 3)) ∧
        s₄.v .v21 = VPermOp.eval (uzp 1) .b16 (s.v (L 2)) (s.v (L 3)) := by
      simp only [s₄, s₃, s₂, s₁, p, v_setV, reduceCtorEq, ite_true, ite_false, h0, h1, h2, h3,
        and_self]
    have i0 : s₈.v .v16 = VPermOp.eval (uzp 1) .b16 (s₄.v .v1) (s₄.v .v21) := by
      simp only [s₈, s₇, s₆, s₅, p, v_setV, reduceCtorEq, ite_true, ite_false]
    have i1 : s₈.v .v17 = VPermOp.eval (uzp 1) .b16 (s₄.v .v0) (s₄.v .v20) := by
      simp only [s₈, s₇, s₆, s₅, p, v_setV, reduceCtorEq, ite_true, ite_false]
    have i2 : s₈.v .v18 = VPermOp.eval (uzp 0) .b16 (s₄.v .v1) (s₄.v .v21) := by
      simp only [s₈, s₇, s₆, s₅, p, v_setV, reduceCtorEq, ite_true, ite_false]
    have i3 : s₈.v .v19 = VPermOp.eval (uzp 0) .b16 (s₄.v .v0) (s₄.v .v20) := by
      simp only [s₈, s₇, s₆, s₅, p, v_setV, reduceCtorEq, ite_true, ite_false]
    simp only [r1.1, r1.2.1, r1.2.2.1, r1.2.2.2] at i0 i1 i2 i3
    intro j hj n hn
    have key : ∀ (o₁ : Nat), o₁ < 2 → ∀ (o₂ : Nat), o₂ < 2 → ∀ x : BitVec 128, x = VPermOp.eval (uzp o₂) .b16
        (VPermOp.eval (uzp o₁) .b16 (s.v (L 0)) (s.v (L 1)))
        (VPermOp.eval (uzp o₁) .b16 (s.v (L 2)) (s.v (L 3))) →
        vbyte x n = vbyte (s.v (L (n / 4))) (4 * (n % 4) + (o₁ + 2 * o₂)) := by
      intro o₁ h₁ o₂ h₂ x e
      rw [e, uzp_uzp _ _ _ _ h₁ h₂ hn, four_regs _ _ (by omega)]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · exact key 1 (by decide) 1 (by decide) _ i0
    · exact key 0 (by decide) 1 (by decide) _ i1
    · exact key 1 (by decide) 0 (by decide) _ i2
    · exact key 0 (by decide) 0 (by decide) _ i3
  · exact (((((((VOnly.setV s (by simp [planesRegs]) _).trans (VOnly.setV _ (by simp [planesRegs]) _)).trans
      (VOnly.setV _ (by simp [planesRegs]) _)).trans (VOnly.setV _ (by simp [planesRegs]) _)).trans
      (VOnly.setV _ (by simp [planesRegs]) _)).trans (VOnly.setV _ (by simp [planesRegs]) _)).trans
      (VOnly.setV _ (by simp [planesRegs]) _)).trans (VOnly.setV _ (by simp [planesRegs]) _)

/-! ## Back to words -/

/-- The registers `words` writes. -/
def wordsRegs : List VReg := [.v0, .v1, .v20, .v21, .v22, .v23]

theorem words_run (s : State) :
    ∃ s', runBlock isa words s = some s' ∧
      (∀ k < 4, ∀ l < 4, ∀ b < 4, vbyte (s'.v (wordReg k)) (4 * l + b) = vbyte (s.v (outReg b)) (4 * k + l)) ∧
      VOnly wordsRegs s s' := by
  let p (o : Nat) (t : State) (d n m : VReg) := t.setV d (VPermOp.eval (zip o) .b16 (t.v n) (t.v m))
  let s₁ := p 0 s .v0 .v20 .v22
  let s₂ := p 1 s₁ .v1 .v20 .v22
  let s₃ := p 0 s₂ .v20 .v21 .v23
  let s₄ := p 1 s₃ .v22 .v21 .v23
  let s₅ := p 0 s₄ .v21 .v0 .v20
  let s₆ := p 1 s₅ .v23 .v0 .v20
  let s₇ := p 0 s₆ .v0 .v1 .v22
  let s₈ := p 1 s₇ .v1 .v1 .v22
  refine ⟨s₈, ?_, ?_, ?_⟩
  · have e₁ : exec (vperm .zip1 .b16 .v0 (outReg 0) (outReg 2)) s = some s₁ := rfl
    have e₂ : exec (vperm .zip2 .b16 .v1 (outReg 0) (outReg 2)) s₁ = some s₂ := rfl
    have e₃ : exec (vperm .zip1 .b16 (outReg 0) (outReg 1) (outReg 3)) s₂ = some s₃ := rfl
    have e₄ : exec (vperm .zip2 .b16 (outReg 2) (outReg 1) (outReg 3)) s₃ = some s₄ := rfl
    have e₅ : exec (vperm .zip1 .b16 (outReg 1) .v0 (outReg 0)) s₄ = some s₅ := rfl
    have e₆ : exec (vperm .zip2 .b16 (outReg 3) .v0 (outReg 0)) s₅ = some s₆ := rfl
    have e₇ : exec (vperm .zip1 .b16 .v0 .v1 (outReg 2)) s₆ = some s₇ := rfl
    have e₈ : exec (vperm .zip2 .b16 .v1 .v1 (outReg 2)) s₇ = some s₈ := rfl
    rw [words, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_cons,
      e₆, runStep_some, runBlock_cons, e₇, runStep_some, runBlock_cons, e₈, runStep_some, runBlock_nil]
  · let P := fun b => s.v (outReg b)
    have r : s₄.v .v0 = VPermOp.eval (zip 0) .b16 (P 0) (P 2) ∧
        s₄.v .v1 = VPermOp.eval (zip 1) .b16 (P 0) (P 2) ∧
        s₄.v .v20 = VPermOp.eval (zip 0) .b16 (P 1) (P 3) ∧
        s₄.v .v22 = VPermOp.eval (zip 1) .b16 (P 1) (P 3) := by
      simp only [s₄, s₃, s₂, s₁, p, P, v_setV, reduceCtorEq, ite_true, ite_false, outReg,
        List.getD_cons_zero, List.getD_cons_succ, and_self]
    have w0 : s₈.v (wordReg 0) = VPermOp.eval (zip 0) .b16 (s₄.v .v0) (s₄.v .v20) := by
      simp only [s₈, s₇, s₆, s₅, p, wordReg, outReg, List.getD_cons_zero, List.getD_cons_succ, v_setV,
        reduceCtorEq, ite_true, ite_false]
    have w1 : s₈.v (wordReg 1) = VPermOp.eval (zip 1) .b16 (s₄.v .v0) (s₄.v .v20) := by
      simp only [s₈, s₇, s₆, s₅, p, wordReg, outReg, List.getD_cons_zero, List.getD_cons_succ, v_setV,
        reduceCtorEq, ite_true, ite_false]
    have w2 : s₈.v (wordReg 2) = VPermOp.eval (zip 0) .b16 (s₄.v .v1) (s₄.v .v22) := by
      simp only [s₈, s₇, s₆, s₅, p, wordReg, outReg, List.getD_cons_zero, List.getD_cons_succ, v_setV,
        reduceCtorEq, ite_true, ite_false]
    have w3 : s₈.v (wordReg 3) = VPermOp.eval (zip 1) .b16 (s₄.v .v1) (s₄.v .v22) := by
      simp only [s₈, s₇, s₆, s₅, p, wordReg, outReg, List.getD_cons_zero, List.getD_cons_succ, v_setV,
        reduceCtorEq, ite_true, ite_false]
    simp only [r.1, r.2.1, r.2.2.1, r.2.2.2] at w0 w1 w2 w3
    have fourP : ∀ b < 4, four (P 0) (P 1) (P 2) (P 3) b = s.v (outReg b) := fun b hb =>
      four_regs s.v outReg hb
    intro k hk l hl b hb
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [w0, zip_zip _ _ _ _ (by decide) (by decide) hl hb, fourP b hb]
    · rw [w1, zip_zip _ _ _ _ (by decide) (by decide) hl hb, fourP b hb]
    · rw [w2, zip_zip _ _ _ _ (by decide) (by decide) hl hb, fourP b hb]
    · rw [w3, zip_zip _ _ _ _ (by decide) (by decide) hl hb, fourP b hb]
  · exact (((((((VOnly.setV s (by simp [wordsRegs]) _).trans (VOnly.setV _ (by simp [wordsRegs]) _)).trans
      (VOnly.setV _ (by simp [wordsRegs]) _)).trans (VOnly.setV _ (by simp [wordsRegs]) _)).trans
      (VOnly.setV _ (by simp [wordsRegs]) _)).trans (VOnly.setV _ (by simp [wordsRegs]) _)).trans
      (VOnly.setV _ (by simp [wordsRegs]) _)).trans (VOnly.setV _ (by simp [wordsRegs]) _)

end VG.Proof.Blowfish.AArch64
