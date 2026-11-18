module

public import VerifiedGarbage.Spec.Blowfish
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Blowfish.Feistel`, which the modules that import this one used -/

section

/-!
# The Feistel network, round by round

`iter K order m (xL, xR)`: the halves after the first `m` rounds of
`feistel`, before its last swap is undone; `iter_succ` is one more round,
and `feistel_eq` the rest of `feistel` after sixteen.
-/

@[expose] public section

namespace VG.Proof.Blowfish

open VG VG.Spec.Blowfish

/-- One round: `xL ^= P`, `xR ^= F(xL)`, swap. -/
def roundStep (K : Schedule) (order : Nat → Nat) (st : Word × Word) (i : Nat) : Word × Word :=
  let xL := st.1 ^^^ pEntry K (order i)
  (f K xL ^^^ st.2, xL)

def iter (K : Schedule) (order : Nat → Nat) (m : Nat) (st : Word × Word) : Word × Word :=
  (List.range m).foldl (roundStep K order) st

theorem iter_succ (K : Schedule) (order : Nat → Nat) (m : Nat) (st : Word × Word) :
    iter K order (m + 1) st = roundStep K order (iter K order m st) m := by
  simp only [iter, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem feistel_eq (K : Schedule) (order : Nat → Nat) (xL xR : Word) :
    feistel K order xL xR =
      ((iter K order 16 (xL, xR)).2 ^^^ pEntry K (order 17),
        (iter K order 16 (xL, xR)).1 ^^^ pEntry K (order 16)) := by
  simp only [feistel, iter]
  rfl

end VG.Proof.Blowfish

end

end

/-!
# F, one S-box at a time

`fAcc K x j`: F's value after its first `j + 1` S-boxes (S₁[a], + S₂[b],
XOR S₃[c], + S₄[d]); `fAcc K x 3 = f K x`. `quarter x j` is the byte of `x`
that indexes S-box `j`: byte `3 - j`.
-/

@[expose] public section

namespace VG.Proof.Blowfish

open VG VG.Spec.Blowfish

/-- The byte of `x` that indexes S-box `j`: `a`, `b`, `c` or `d`. -/
def quarter (x : Word) (j : Nat) : Byte := x.extractLsb' (8 * (3 - j)) 8

/-- S-box `j` of `x`'s quarter. -/
def sq (K : Schedule) (x : Word) (j : Nat) : Word := sEntry K j (quarter x j)

def fAcc (K : Schedule) (x : Word) : Nat → Word
  | 0 => sq K x 0
  | 1 => sq K x 0 + sq K x 1
  | 2 => (sq K x 0 + sq K x 1) ^^^ sq K x 2
  | _ => ((sq K x 0 + sq K x 1) ^^^ sq K x 2) + sq K x 3

/-- One S-box step of F, from the previous steps' `prev`, for any schedule `K`
(so that no proof evaluates a concrete schedule's S-boxes). -/
theorem fAcc_step (K : Schedule) (x : Word) {j : Nat} (hj : j < 4) (prev : Word)
    (hp : 0 < j → prev = fAcc K x (j - 1)) :
    (if j = 0 then sq K x j else if j = 2 then prev ^^^ sq K x j else prev + sq K x j) = fAcc K x j := by
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · rfl
  · rw [hp (by decide)]; rfl
  · rw [hp (by decide)]; rfl
  · rw [hp (by decide)]; rfl

theorem shift_setWidth (x : Word) (k : Nat) : (x >>> k).setWidth 8 = x.extractLsb' k 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem fAcc_three (K : Schedule) (x : Word) : fAcc K x 3 = f K x := by
  have h0 : x.setWidth 8 = x.extractLsb' 0 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
  simp only [fAcc, sq, f, quarter, shift_setWidth x 24, shift_setWidth x 16, shift_setWidth x 8, h0,
    Nat.reduceSub, Nat.reduceMul]

end VG.Proof.Blowfish
