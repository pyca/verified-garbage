module

public import VerifiedGarbage.Proof.Blowfish.AArch64.Sbox
public import VerifiedGarbage.Proof.Blowfish.F
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Blowfish.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Blowfish.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Blowfish.AArch64.F`, which only this module used -/

section

/-! ### `Blowfish.AArch64.Planes`, which only this module used -/

section

/-! ### `Blowfish.AArch64.Transpose`, which only this module used -/

section

/-!
# Words to byte planes and back

`uzp_uzp`: two levels of `uzp1`/`uzp2` (as in `planes`) leave in byte `n`
of the result byte `o₁ + 2 o₂` of word `n` of four vectors (`o₁`, `o₂` 0 for
`uzp1` and 1 for `uzp2`). `zip_zip`: two levels of `zip1`/`zip2` (as in
`words`) turn four byte planes back into sixteen words.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64

/-- `uzp1` (`o = 0`) or `uzp2` (`o = 1`). -/
def uzp (o : Nat) : VPermOp := if o = 0 then .uzp1 else .uzp2

theorem vbyte_uzp (o : Nat) (ho : o < 2) (x y : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (VPermOp.eval (uzp o) .b16 x y) e =
      if e < 8 then vbyte x (2 * e + o) else vbyte y (2 * e + o - 16) := by
  rcases (by omega_using [ho] : o = 0 ∨ o = 1) with rfl | rfl
  · exact vbyte_uzp1 x y he
  · exact vbyte_uzp2 x y he

/-- Word `k` of four vectors. -/
def four (W0 W1 W2 W3 : BitVec 128) (k : Nat) : BitVec 128 := [W0, W1, W2, W3].getD k 0

theorem uzp_uzp (W0 W1 W2 W3 : BitVec 128) {o₁ o₂ : Nat} (h₁ : o₁ < 2) (h₂ : o₂ < 2) {n : Nat}
    (hn : n < 16) :
    vbyte (VPermOp.eval (uzp o₂) .b16 (VPermOp.eval (uzp o₁) .b16 W0 W1)
        (VPermOp.eval (uzp o₁) .b16 W2 W3)) n =
      vbyte (four W0 W1 W2 W3 (n / 4)) (4 * (n % 4) + (o₁ + 2 * o₂)) := by
  rw [vbyte_uzp _ h₂ _ _ hn]
  split
  · rw [vbyte_uzp _ h₁ _ _ (by omega_arith)]
    split
    · rw [show n / 4 = 0 by omega_arith]; exact congrArg _ (by omega_arith)
    · rw [show n / 4 = 1 by omega_arith]; exact congrArg _ (by omega_arith)
  · rw [vbyte_uzp _ h₁ _ _ (by omega_using [h₂, hn])]
    split
    · rw [show n / 4 = 2 by omega_arith]; exact congrArg _ (by omega_arith)
    · rw [show n / 4 = 3 by omega_arith]; exact congrArg _ (by omega_arith)

/-- `zip1` (`o = 0`) or `zip2` (`o = 1`). -/
def zip (o : Nat) : VPermOp := if o = 0 then .zip1 else .zip2

theorem vbyte_zip (o : Nat) (ho : o < 2) (x y : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (VPermOp.eval (zip o) .b16 x y) e =
      if e % 2 = 0 then vbyte x (8 * o + e / 2) else vbyte y (8 * o + e / 2) := by
  rcases (by omega_using [ho] : o = 0 ∨ o = 1) with rfl | rfl
  · rw [show zip 0 = .zip1 from rfl, vbyte_zip1 x y he]; simp
  · exact vbyte_zip2 x y he

/-- Byte `b` of word `l` of `zip o₂ (zip o₁ P0 P2) (zip o₁ P1 P3)` is byte
`4 (2 o₁ + o₂) + l` of plane `b`: word `4 k + l` with `k = 2 o₁ + o₂`. -/
theorem zip_zip (P0 P1 P2 P3 : BitVec 128) {o₁ o₂ : Nat} (h₁ : o₁ < 2) (h₂ : o₂ < 2) {l b : Nat}
    (hl : l < 4) (hb : b < 4) :
    vbyte (VPermOp.eval (zip o₂) .b16 (VPermOp.eval (zip o₁) .b16 P0 P2)
        (VPermOp.eval (zip o₁) .b16 P1 P3)) (4 * l + b) =
      vbyte (four P0 P1 P2 P3 b) (4 * (2 * o₁ + o₂) + l) := by
  rw [vbyte_zip _ h₂ _ _ (by omega_using [hl, hb])]
  split
  · rw [vbyte_zip _ h₁ _ _ (by omega_using [h₂, hl, hb])]
    split
    · rw [show b = 0 by omega_arith]; exact congrArg _ (by omega_using [])
    · rw [show b = 2 by omega_arith]; exact congrArg _ (by omega_using [])
  · rw [vbyte_zip _ h₁ _ _ (by omega_using [h₂, hl, hb])]
    split
    · rw [show b = 1 by omega_arith]; exact congrArg _ (by omega_using [])
    · rw [show b = 3 by omega_arith]; exact congrArg _ (by omega_using [])

end VG.Proof.Blowfish.AArch64

end

end


/-!
# Byte planes in and out, and the accumulation of F

`planes_run`: `planes L` leaves in `idxReg j` byte `3 - j` of each word of
`L`. `words_run`: `words` turns the byte planes in `outReg` into words.
`combine_run`: `combine j` accumulates them into `fReg`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.AArch64.Tbl (VOnly)

/-- The registers `planes` writes. -/
def planesRegs : List VReg := [.v0, .v1, .v20, .v21, .v16, .v17, .v18, .v19]

theorem four_regs (v : VReg → BitVec 128) (L : Nat → VReg) {k : Nat} (hk : k < 4) :
    four (v (L 0)) (v (L 1)) (v (L 2)) (v (L 3)) k = v (L k) := by
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

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
      rw [e, uzp_uzp _ _ _ _ h₁ h₂ hn, four_regs _ _ (by omega_using [hn])]
    rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
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
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [w0, zip_zip _ _ _ _ (by decide) (by decide) hl hb, fourP b hb]
    · rw [w1, zip_zip _ _ _ _ (by decide) (by decide) hl hb, fourP b hb]
    · rw [w2, zip_zip _ _ _ _ (by decide) (by decide) hl hb, fourP b hb]
    · rw [w3, zip_zip _ _ _ _ (by decide) (by decide) hl hb, fourP b hb]
  · exact (((((((VOnly.setV s (by simp [wordsRegs]) _).trans (VOnly.setV _ (by simp [wordsRegs]) _)).trans
      (VOnly.setV _ (by simp [wordsRegs]) _)).trans (VOnly.setV _ (by simp [wordsRegs]) _)).trans
      (VOnly.setV _ (by simp [wordsRegs]) _)).trans (VOnly.setV _ (by simp [wordsRegs]) _)).trans
      (VOnly.setV _ (by simp [wordsRegs]) _)).trans (VOnly.setV _ (by simp [wordsRegs]) _)

end VG.Proof.Blowfish.AArch64

end

end


/-!
# F on sixteen words

`f_run`: from the byte planes of sixteen words `x n` in `idxReg` (`planes`),
`f sch` leaves `F(x n)` in word `n % 4` of `fReg (n / 4)`, under the
schedule at `sch`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

/-- What `combine j` does to a register of F and a register of words. -/
def cop (j : Nat) (x y : BitVec 128) : BitVec 128 :=
  if j = 0 then y else if j = 2 then x ^^^ y else VArr.s4.map2 (fun _ a b => a + b) x y

theorem vword_cop (j : Nat) (x y : BitVec 128) {l : Nat} (hl : l < 4) :
    vword (cop j x y) l =
      if j = 0 then vword y l else if j = 2 then vword x l ^^^ vword y l else vword x l + vword y l := by
  simp only [cop]
  split
  · rfl
  · split
    · exact vword_xor x y l
    · exact vword_map2 _ x y hl

theorem exec_combine (s : State) (j : Nat) {k : Nat} (hk : k < 4) :
    exec ((combine j).getD k (.vop (.movi0 .v0))) s =
      some (s.setV (fReg k) (cop j (s.v (fReg k)) (s.v (wordReg k)))) := by
  simp only [combine, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some, cop]
  split
  · rfl
  · split <;> rfl

def fRegs : List VReg := [.v12, .v13, .v14, .v15]

theorem wordReg_ne_fReg : ∀ k < 4, ∀ k' < 4, wordReg k ≠ fReg k' := by decide
theorem fReg_ne : ∀ k < 4, ∀ k' < 4, k ≠ k' → fReg k ≠ fReg k' := by decide

theorem combine_run (s : State) (j : Nat) :
    ∃ s', runBlock isa (combine j) s = some s' ∧
      (∀ k < 4, s'.v (fReg k) = cop j (s.v (fReg k)) (s.v (wordReg k))) ∧ VOnly fRegs s s' := by
  let t (k : Nat) (u : State) := u.setV (fReg k) (cop j (u.v (fReg k)) (u.v (wordReg k)))
  let s₁ := t 0 s
  let s₂ := t 1 s₁
  let s₃ := t 2 s₂
  let s₄ := t 3 s₃
  have e : ∀ (k : Nat) (u : State), k < 4 →
      exec ((combine j).getD k (.vop (.movi0 .v0))) u = some (t k u) := fun k u hk => by
    rw [exec_combine _ _ hk]
  have hl : combine j = [(combine j).getD 0 (.vop (.movi0 .v0)), (combine j).getD 1 (.vop (.movi0 .v0)),
      (combine j).getD 2 (.vop (.movi0 .v0)), (combine j).getD 3 (.vop (.movi0 .v0))] := by
    simp only [combine, List.getD_eq_getElem?_getD]; rfl
  refine ⟨s₄, ?_, ?_, ?_⟩
  · rw [hl, runBlock_cons, e 0 s (by decide), runStep_some, runBlock_cons, e 1 s₁ (by decide),
      runStep_some, runBlock_cons, e 2 s₂ (by decide), runStep_some, runBlock_cons,
      e 3 s₃ (by decide), runStep_some, runBlock_nil]
  · have wk : ∀ k < 4, ∀ (u : State) (k' : Nat), k' < 4 → (t k' u).v (wordReg k) = u.v (wordReg k) :=
      fun k hk u k' hk' => v_setV_of_ne _ _ (wordReg_ne_fReg k hk k' hk')
    have fk : ∀ k < 4, ∀ (u : State) (k' : Nat), k' < 4 → k ≠ k' → (t k' u).v (fReg k) = u.v (fReg k) :=
      fun k hk u k' hk' hne => v_setV_of_ne _ _ (fReg_ne k hk k' hk' hne)
    intro k hk
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [fk 0 (by decide) _ 3 (by decide) (by decide), fk 0 (by decide) _ 2 (by decide) (by decide),
        fk 0 (by decide) _ 1 (by decide) (by decide)]
      exact v_setV_self _ _ _
    · rw [fk 1 (by decide) _ 3 (by decide) (by decide), fk 1 (by decide) _ 2 (by decide) (by decide)]
      show (s₁.setV _ _).v _ = _
      rw [v_setV_self, fk 1 (by decide) _ 0 (by decide) (by decide), wk 1 (by decide) _ 0 (by decide)]
    · rw [fk 2 (by decide) _ 3 (by decide) (by decide)]
      show (s₂.setV _ _).v _ = _
      rw [v_setV_self, fk 2 (by decide) _ 1 (by decide) (by decide), fk 2 (by decide) _ 0 (by decide) (by decide),
        wk 2 (by decide) _ 1 (by decide), wk 2 (by decide) _ 0 (by decide)]
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_self, fk 3 (by decide) _ 2 (by decide) (by decide), fk 3 (by decide) _ 1 (by decide) (by decide),
        fk 3 (by decide) _ 0 (by decide) (by decide), wk 3 (by decide) _ 2 (by decide),
        wk 3 (by decide) _ 1 (by decide), wk 3 (by decide) _ 0 (by decide)]
  · exact (((VOnly.setV s (by simp [fRegs, fReg]) _).trans (VOnly.setV _ (by simp [fRegs, fReg]) _)).trans
      (VOnly.setV _ (by simp [fRegs, fReg]) _)).trans (VOnly.setV _ (by simp [fRegs, fReg]) _)

/-! ## One S-box of F -/

/-- Word `n` of sixteen in the registers `R`. -/
def lane (v : VReg → BitVec 128) (R : Nat → VReg) (n : Nat) : Word := vword (v (R (n / 4))) (n % 4)

def stepRegs : List VReg := lookupRegs ++ wordsRegs ++ fRegs

theorem fReg_notin : ∀ k < 4, fReg k ∉ lookupRegs ∧ fReg k ∉ wordsRegs := by decide

theorem sbox_run {s : State} {sch : Reg} (hR : Readable s sch) (hc : Consts s) {j : Nat} (hj : j < 4)
    (x : Nat → Word) (hx : ∀ n < 16, vbyte (s.v (idxReg j)) n = quarter (x n) j)
    (hprev : 0 < j → ∀ n < 16, lane s.v fReg n = fAcc (scheduleAt s.mem (s.gpr sch)) (x n) (j - 1)) :
    ∃ s', runBlock isa (lookup sch j ++ words ++ combine j) s = some s' ∧
      (∀ n < 16, lane s'.v fReg n = fAcc (scheduleAt s.mem (s.gpr sch)) (x n) j) ∧
      VOnly stepRegs s s' := by
  let K := scheduleAt s.mem (s.gpr sch)
  obtain ⟨s₁, r₁, v₁, o₁⟩ := lookup_run hR hc hj
  obtain ⟨s₂, r₂, v₂, o₂⟩ := words_run s₁
  obtain ⟨s₃, r₃, v₃, o₃⟩ := combine_run s₂ j
  refine ⟨s₃, VG.AArch64.Tbl.runBlock_cat_some (VG.AArch64.Tbl.runBlock_cat_some r₁ r₂) r₃, ?_, ?_⟩
  · intro n hn
    have hk : n / 4 < 4 := by omega_using [hn]
    have hl : n % 4 < 4 := by omega_using []
    -- the words of S-box `j`
    have w : vword (s₂.v (wordReg (n / 4))) (n % 4) = sq K (x n) j := by
      refine word_ext fun b hb => ?_
      rw [← vbyte_word _ hb, v₂ _ hk _ hl _ hb, show 4 * (n / 4) + n % 4 = n by omega_using [], v₁ _ hb _ hn, hx n hn,
        sq, sEntry_byte _ _ hj hb]
      rfl
    have f₂ : s₂.v (fReg (n / 4)) = s.v (fReg (n / 4)) := by
      rw [o₂.2 _ (fReg_notin _ hk).2, o₁.2 _ (fReg_notin _ hk).1]
    simp only [lane]
    rw [v₃ _ hk, vword_cop _ _ _ hl, w, f₂]
    exact fAcc_step K (x n) hj _ fun h => hprev h n hn
  · exact ((VOnly.mono o₁ (by decide)).trans (VOnly.mono o₂ (by decide))).trans (VOnly.mono o₃ (by decide))

theorem idx_notin_step : ∀ j < 4, idxReg j ∉ stepRegs := by decide
theorem const_notin_step : c64 ∉ stepRegs ∧ c128 ∉ stepRegs := by decide

theorem f_eq (sch : Reg) :
    f sch = (lookup sch 0 ++ words ++ combine 0) ++ ((lookup sch 1 ++ words ++ combine 1) ++
      ((lookup sch 2 ++ words ++ combine 2) ++ ((lookup sch 3 ++ words ++ combine 3) ++ []))) := rfl

/-- F of sixteen words whose byte planes are in `idxReg`. -/
theorem f_run {s : State} {sch : Reg} (hR : Readable s sch) (hc : Consts s) (x : Nat → Word)
    (hx : ∀ j < 4, ∀ n < 16, vbyte (s.v (idxReg j)) n = quarter (x n) j) :
    ∃ s', runBlock isa (f sch) s = some s' ∧
      (∀ n < 16, lane s'.v fReg n = Spec.Blowfish.f (scheduleAt s.mem (s.gpr sch)) (x n)) ∧
      VOnly stepRegs s s' := by
  have keep : ∀ {t : State}, VOnly stepRegs s t →
      Readable t sch ∧ Consts t ∧ (∀ j < 4, ∀ n < 16, vbyte (t.v (idxReg j)) n = quarter (x n) j) ∧
        t.mem = s.mem ∧ t.gpr = s.gpr := by
    intro t ht
    refine ⟨fun off hoff => ?_, ⟨fun e he => ?_, fun e he => ?_⟩, fun j hj n hn => ?_, ht.mem, ht.gpr⟩
    · rw [ht.rd, ht.wr, ht.gpr]; exact hR off hoff
    · rw [ht.2 _ const_notin_step.1]; exact hc.1 e he
    · rw [ht.2 _ const_notin_step.2]; exact hc.2 e he
    · rw [ht.2 _ (idx_notin_step j hj)]; exact hx j hj n hn
  obtain ⟨s₀, r₀, v₀, o₀⟩ := sbox_run hR hc (by decide : 0 < 4) x (hx 0 (by decide)) (by intro h; omega)
  have k₀ := keep o₀
  obtain ⟨s₁, r₁, v₁, o₁⟩ := sbox_run k₀.1 k₀.2.1 (by decide : 1 < 4) x (k₀.2.2.1 1 (by decide))
    (fun _ n hn => by rw [v₀ n hn, k₀.2.2.2.1, k₀.2.2.2.2])
  have p₁ := o₀.trans o₁
  have k₁ := keep p₁
  obtain ⟨s₂, r₂, v₂, o₂⟩ := sbox_run k₁.1 k₁.2.1 (by decide : 2 < 4) x (k₁.2.2.1 2 (by decide))
    (fun _ n hn => by rw [v₁ n hn, k₀.2.2.2.1, k₀.2.2.2.2, k₁.2.2.2.1, k₁.2.2.2.2])
  have p₂ := p₁.trans o₂
  have k₂ := keep p₂
  obtain ⟨s₃, r₃, v₃, o₃⟩ := sbox_run k₂.1 k₂.2.1 (by decide : 3 < 4) x (k₂.2.2.1 3 (by decide))
    (fun _ n hn => by rw [v₂ n hn, k₁.2.2.2.1, k₁.2.2.2.2, k₂.2.2.2.1, k₂.2.2.2.2])
  have p₃ := p₂.trans o₃
  refine ⟨s₃, ?_, fun n hn => ?_, p₃⟩
  · rw [f_eq]
    exact VG.AArch64.Tbl.runBlock_cat_some r₀ (VG.AArch64.Tbl.runBlock_cat_some r₁
      (VG.AArch64.Tbl.runBlock_cat_some r₂ (VG.AArch64.Tbl.runBlock_cat_some r₃ runBlock_nil)))
  · rw [v₃ n hn, k₂.2.2.2.1, k₂.2.2.2.2, fAcc_three]

end VG.Proof.Blowfish.AArch64

end

end


/-!
# One round on sixteen blocks

`round_run`: `round sch up L R`, with `x5` at Pᵢ₊₁ in the schedule at `sch`,
leaves `L ^ Pᵢ₊₁` in `L` and `R ^ F(L ^ Pᵢ₊₁)` in `R`, word by word, and
moves `x5` to the next entry (`up`) or the previous one.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

/-- Only the general-purpose registers `gs` and the vector registers `vs` change. -/
structure Only (gs : List Reg) (vs : List VReg) (s s' : State) : Prop where
  eq : s' = { s with gpr := s'.gpr, v := s'.v }
  g : ∀ r, r ∉ gs → s'.gpr r = s.gpr r
  v : ∀ r, r ∉ vs → s'.v r = s.v r

theorem Only.trans {gs : List Reg} {vs : List VReg} {a b c : State} (h₁ : Only gs vs a b) (h₂ : Only gs vs b c) :
    Only gs vs a c := by
  refine ⟨?_, fun r hr => (h₂.g r hr).trans (h₁.g r hr), fun r hr => (h₂.v r hr).trans (h₁.v r hr)⟩
  rw [h₂.eq, h₁.eq]

theorem Only.mono {gs gs' : List Reg} {vs vs' : List VReg} {a b : State} (h : Only gs vs a b)
    (hg : ∀ r ∈ gs, r ∈ gs') (hv : ∀ r ∈ vs, r ∈ vs') : Only gs' vs' a b :=
  ⟨h.eq, fun r hr => h.g r fun h' => hr (hg r h'), fun r hr => h.v r fun h' => hr (hv r h')⟩

theorem Only.ofV {vs : List VReg} {a b : State} (h : VOnly vs a b) : Only [] vs a b := by
  refine ⟨?_, fun r _ => ?_, h.2⟩
  · rw [h.1]
  · rw [h.1]

theorem Only.mem {gs : List Reg} {vs : List VReg} {a b : State} (h : Only gs vs a b) : b.mem = a.mem := by
  rw [h.eq]
theorem Only.rd {gs : List Reg} {vs : List VReg} {a b : State} (h : Only gs vs a b) : b.rd = a.rd := by
  rw [h.eq]
theorem Only.wr {gs : List Reg} {vs : List VReg} {a b : State} (h : Only gs vs a b) : b.wr = a.wr := by
  rw [h.eq]
theorem Only.sp {gs : List Reg} {vs : List VReg} {a b : State} (h : Only gs vs a b) : b.sp = a.sp := by
  rw [h.eq]

/-- The schedule at `sch` is readable. -/
def SchedIn (s : State) (sch : Reg) : Prop :=
  ∀ off n, off + n ≤ 4168 → InRegions (s.rd ++ s.wr) (s.gpr sch + BitVec.ofNat 64 off) n

theorem SchedIn.readable {s : State} {sch : Reg} (h : SchedIn s sch) : Readable s sch :=
  fun off hoff => h off 16 (by omega_using [hoff])

/-- The registers of the halves. -/
def halfRegs : List VReg := [.v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11]

/-- What a round writes: `v0` and the registers of `planes` and `f`, and the halves. -/
def roundRegs : List VReg := .v0 :: planesRegs ++ stepRegs ++ halfRegs

/-- Halves `L` and `R`: `A` and `B` (`v4`–`v11`), in either role. -/
structure Halves (L R : Nat → VReg) : Prop where
  inL : ∀ k < 4, L k ∈ halfRegs
  inR : ∀ k < 4, R k ∈ halfRegs
  injL : ∀ k < 4, ∀ k' < 4, k ≠ k' → L k ≠ L k'
  injR : ∀ k < 4, ∀ k' < 4, k ≠ k' → R k ≠ R k'
  ne : ∀ k < 4, ∀ k' < 4, L k ≠ R k'

theorem halves_ab : Halves aReg bReg := ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem halves_ba : Halves bReg aReg := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem half_notin : ∀ r ∈ halfRegs, r ∉ planesRegs ∧ r ∉ stepRegs ∧ r ≠ .v0 := by decide

/-- XOR of a register with `v0`, for each of the four registers of a half `H`. -/
def xorHalf (H : Nat → VReg) (S : Nat → VReg) : List Instr :=
  (List.range 4).map fun k => veor (H k) (H k) (S k)

theorem xorHalf_run (s : State) {H S : Nat → VReg} (hinj : ∀ k < 4, ∀ k' < 4, k ≠ k' → H k ≠ H k')
    (hS : ∀ k < 4, ∀ k' < 4, S k ≠ H k') :
    ∃ s', runBlock isa (xorHalf H S) s = some s' ∧
      (∀ k < 4, s'.v (H k) = s.v (H k) ^^^ s.v (S k)) ∧ Only [] [H 0, H 1, H 2, H 3] s s' := by
  let t (k : Nat) (u : State) := u.setV (H k) (u.v (H k) ^^^ u.v (S k))
  let s₁ := t 0 s
  let s₂ := t 1 s₁
  let s₃ := t 2 s₂
  let s₄ := t 3 s₃
  refine ⟨s₄, ?_, ?_, ?_⟩
  · have e : ∀ k (u : State), exec (veor (H k) (H k) (S k)) u = some (t k u) := fun _ _ => rfl
    show runBlock isa [veor (H 0) (H 0) (S 0), veor (H 1) (H 1) (S 1), veor (H 2) (H 2) (S 2),
      veor (H 3) (H 3) (S 3)] s = _
    rw [runBlock_cons, e, runStep_some, runBlock_cons, e, runStep_some, runBlock_cons, e, runStep_some,
      runBlock_cons, e, runStep_some, runBlock_nil]
  · have hh : ∀ k < 4, ∀ k' < 4, k ≠ k' → ∀ u : State, (t k' u).v (H k) = u.v (H k) :=
      fun k hk k' hk' hne u => v_setV_of_ne _ _ (hinj k hk k' hk' hne)
    have hs : ∀ k < 4, ∀ k' < 4, ∀ u : State, (t k' u).v (S k) = u.v (S k) :=
      fun k hk k' hk' u => v_setV_of_ne _ _ (hS k hk k' hk')
    intro k hk
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [hh 0 (by decide) 3 (by decide) (by decide), hh 0 (by decide) 2 (by decide) (by decide),
        hh 0 (by decide) 1 (by decide) (by decide)]
      exact v_setV_self _ _ _
    · rw [hh 1 (by decide) 3 (by decide) (by decide), hh 1 (by decide) 2 (by decide) (by decide)]
      show (s₁.setV _ _).v _ = _
      rw [v_setV_self, hh 1 (by decide) 0 (by decide) (by decide), hs 1 (by decide) 0 (by decide)]
    · rw [hh 2 (by decide) 3 (by decide) (by decide)]
      show (s₂.setV _ _).v _ = _
      rw [v_setV_self, hh 2 (by decide) 1 (by decide) (by decide), hh 2 (by decide) 0 (by decide) (by decide),
        hs 2 (by decide) 1 (by decide), hs 2 (by decide) 0 (by decide)]
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_self, hh 3 (by decide) 2 (by decide) (by decide), hh 3 (by decide) 1 (by decide) (by decide),
        hh 3 (by decide) 0 (by decide) (by decide), hs 3 (by decide) 2 (by decide),
        hs 3 (by decide) 1 (by decide), hs 3 (by decide) 0 (by decide)]
  · exact Only.ofV ((((VOnly.setV s (by simp) _).trans (VOnly.setV _ (by simp) _)).trans
      (VOnly.setV _ (by simp) _)).trans (VOnly.setV _ (by simp) _))

theorem round_eq (sch : Reg) (up : Bool) (L R : Nat → VReg) :
    round sch up L R = loadP ++ xorHalf L (fun _ => .v0) ++ planes L ++ f sch ++ xorHalf R fReg ++
      [if up then .addImm .x .x5 .x5 4 else .subImm .x .x5 .x5 4] := rfl

theorem quarter_lane (x : BitVec 128) {n j : Nat} (hj : j < 4) :
    vbyte x (4 * (n % 4) + (3 - j)) = quarter (vword x (n % 4)) j := by
  rw [vbyte_word _ (by omega)]; rfl

theorem fReg_ne_half : ∀ k < 4, ∀ r ∈ halfRegs, fReg k ≠ r := by decide

theorem round_run {s : State} {sch : Reg} (hS : SchedIn s sch) (hc : Consts s) (up : Bool)
    {L R : Nat → VReg} (H : Halves L R) {i : Nat} (hi : i < 18)
    (hx5 : s.gpr .x5 = s.gpr sch + BitVec.ofNat 64 (4 * i)) (hsch : sch ≠ .x5 ∧ sch ≠ .x6) :
    ∃ s', runBlock isa (round sch up L R) s = some s' ∧
      (∀ n < 16, lane s'.v L n = lane s.v L n ^^^ pEntry (scheduleAt s.mem (s.gpr sch)) i) ∧
      (∀ n < 16, lane s'.v R n = lane s.v R n ^^^
        Spec.Blowfish.f (scheduleAt s.mem (s.gpr sch)) (lane s.v L n ^^^ pEntry (scheduleAt s.mem (s.gpr sch)) i)) ∧
      s'.gpr .x5 = (if up then s.gpr .x5 + 4 else s.gpr .x5 - 4) ∧
      Only [.x5, .x6] roundRegs s s' := by
  let K := scheduleAt s.mem (s.gpr sch)
  let p := pEntry K i
  -- the P-array entry
  have hp : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 pOff) 4 := by
    rw [hx5, Offset.add_add]; exact hS _ _ (by simp only [pOff]; omega_using [hi])
  have hread : s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 pOff) 32 = p := by
    rw [hx5, Offset.add_add, show 4 * i + pOff = 4096 + 4 * i by simp only [pOff]; omega_using []]
    exact (pEntry_read _ _ hi).symm
  let s₁ := s.write .w .x6 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 pOff) 32)
  let s₂ := s₁.setV .v0 (let w := (s₁.gpr .x6).setWidth 32; ofVWords w w w w)
  have r₂ : runBlock isa loadP s = some s₂ := by
    rw [loadP, runBlock_cons, exec_ldr_w (by simp only [pOff]; decide) hp, runStep_some, runBlock_cons,
      exec_dup4, runStep_some, runBlock_nil]
  have v0₂ : ∀ l < 4, vword (s₂.v .v0) l = p := by
    intro l hl
    simp only [s₂, v_setV_self]
    rw [vword_ofVWords _ _ _ _ hl]
    have : (s₁.gpr .x6).setWidth 32 = p := by
      simp only [s₁, gpr_write_self, ← hread]; exact BitVec.setWidth_setWidth_of_le _ (by omega_using []) |>.trans (by simp)
    rcases (by omega_using [hl] : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> exact this
  have o₂ : Only [.x6] [.v0] s s₂ := by
    refine ⟨rfl, fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_singleton] at hr
      simp only [s₂, s₁, gpr_setV, gpr_write_of_ne _ _ _ hr]
    · simp only [List.mem_singleton] at hr
      exact v_setV_of_ne _ _ hr
  have hL := fun k hk => half_notin _ (H.inL k hk)
  have hR := fun k hk => half_notin _ (H.inR k hk)
  -- L ^= P
  obtain ⟨s₃, r₃, v₃, o₃⟩ := xorHalf_run s₂ H.injL (S := fun _ => .v0) fun k _ k' hk' => (hL k' hk').2.2.symm
  have L₃ : ∀ n < 16, lane s₃.v L n = lane s.v L n ^^^ p := by
    intro n hn
    simp only [lane]
    rw [v₃ _ (by omega_using [hn]), vword_xor, v0₂ _ (by omega_using []), o₂.v _ (by simp; exact (hL _ (by omega_using [hn])).2.2)]
  -- the planes
  obtain ⟨s₄, r₄, v₄, o₄⟩ := planes_run s₃ L fun k hk => (hL k hk).1
  -- F
  have o₂₄ : Only [.x6] roundRegs s s₄ := (o₂.mono (by simp) (by simp [roundRegs])).trans
    ((o₃.mono (by simp) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h <;> subst h <;>
          exact List.mem_append_right _ (H.inL _ (by decide))).trans
      ((Only.ofV o₄).mono (by simp) (fun r hr => by simp [roundRegs, hr])))
  have hS₄ : Readable s₄ sch := fun off hoff => by
    rw [o₂₄.rd, o₂₄.wr, o₂₄.g _ (by simp; exact hsch.2)]; exact hS.readable off hoff
  have hc₄ : Consts s₄ := by
    have n64 : c64 ∉ roundRegs := by decide
    have n128 : c128 ∉ roundRegs := by decide
    exact ⟨fun e he => by rw [o₂₄.v _ n64]; exact hc.1 e he, fun e he => by rw [o₂₄.v _ n128]; exact hc.2 e he⟩
  obtain ⟨s₅, r₅, v₅, o₅⟩ := f_run hS₄ hc₄ (lane s₃.v L) fun j hj n hn => by
    rw [v₄ j hj n hn, quarter_lane _ hj]; rfl
  have K₅ : scheduleAt s₄.mem (s₄.gpr sch) = K := by
    rw [o₂₄.mem, o₂₄.g _ (by simp; exact hsch.2)]
  -- R ^= F
  obtain ⟨s₆, r₆, v₆, o₆⟩ := xorHalf_run s₅ H.injR (S := fReg) fun k hk k' hk' =>
    fReg_ne_half k hk _ (H.inR k' hk')
  let s₇ := s₆.write .x .x5 (if up then s₆.read .x .x5 + BitVec.ofNat _ 4 else s₆.read .x .x5 - BitVec.ofNat _ 4)
  have r₇ : runBlock isa [if up then .addImm .x .x5 .x5 4 else .subImm .x .x5 .x5 4] s₆ = some s₇ := by
    cases up
    · rw [runBlock_cons]; simp only [Bool.false_eq_true, ite_false]
      rw [exec_subImm_x (by decide), runStep_some, runBlock_nil]; rfl
    · rw [runBlock_cons]; simp only [ite_true]
      rw [exec_addImm_x (by decide), runStep_some, runBlock_nil]; rfl
  have o₂₆ : Only [.x6] roundRegs s s₆ := o₂₄.trans (((Only.ofV o₅).mono (by simp) (fun r hr => by simp [roundRegs, hr])).trans
    (o₆.mono (by simp) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h <;> subst h <;>
          exact List.mem_append_right _ (H.inR _ (by decide))))
  have o₇ : Only [.x5, .x6] roundRegs s s₇ := by
    refine (o₂₆.mono (by simp) (fun _ h => h)).trans ⟨rfl, fun r hr => ?_, fun _ _ => rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [s₇, gpr_write_of_ne _ _ _ hr.1]
  refine ⟨s₇, ?_, ?_, ?_, ?_, o₇⟩
  · rw [round_eq]
    exact VG.AArch64.Tbl.runBlock_cat_some (VG.AArch64.Tbl.runBlock_cat_some
      (VG.AArch64.Tbl.runBlock_cat_some (VG.AArch64.Tbl.runBlock_cat_some
        (VG.AArch64.Tbl.runBlock_cat_some r₂ r₃) r₄) r₅) r₆) r₇
  · intro n hn
    have hk : n / 4 < 4 := by omega_using [hn]
    have nr : ∀ k < 4, L k ∉ [R 0, R 1, R 2, R 3] := fun k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨H.ne k hk 0 (by decide), H.ne k hk 1 (by decide), H.ne k hk 2 (by decide), H.ne k hk 3 (by decide)⟩
    simp only [lane] at L₃ ⊢
    rw [show s₇.v = s₆.v from rfl, o₆.v _ (nr _ hk), o₅.2 _ (hL _ hk).2.1, o₄.2 _ (hL _ hk).1, L₃ n hn]
  · intro n hn
    have hk : n / 4 < 4 := by omega_using [hn]
    have nl : R (n / 4) ∉ [L 0, L 1, L 2, L 3] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(H.ne 0 (by decide) _ hk).symm, (H.ne 1 (by decide) _ hk).symm,
        (H.ne 2 (by decide) _ hk).symm, (H.ne 3 (by decide) _ hk).symm⟩
    have hRv : s₅.v (R (n / 4)) = s.v (R (n / 4)) := by
      rw [o₅.2 _ (hR _ hk).2.1, o₄.2 _ (hR _ hk).1, o₃.v _ nl,
        o₂.v _ (by simp; exact (hR _ hk).2.2)]
    have L₃n := L₃ n hn
    simp only [lane] at v₅ L₃n ⊢
    rw [show s₇.v = s₆.v from rfl, v₆ _ hk, vword_xor, v₅ n hn, K₅, L₃n, hRv]
  · simp only [s₇, gpr_write_self, State.read, BitVec.setWidth_eq]
    rw [o₂₆.g _ (by simp)]
    cases up <;> rfl

end VG.Proof.Blowfish.AArch64
