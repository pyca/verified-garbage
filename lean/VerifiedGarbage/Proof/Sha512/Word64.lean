import VerifiedGarbage.Spec.Sha512
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Spec.Sha256

/- Proofs formerly in `VerifiedGarbage.Proof.Sha512.Spec`. -/
section

/-!
# SHA-512: lemmas about the specification
-/

namespace VG.Proof.Sha512

open VG.Spec.Sha512

/-! ## The message schedule -/

theorem schedule_succ (M : VG.Spec.Sha512.Block) (t : Nat) : VG.Spec.Sha512.schedule M (t + 1) = VG.Spec.Sha512.W M t :: VG.Spec.Sha512.schedule M t := rfl

theorem schedule_getElem! (M : VG.Spec.Sha512.Block) {t i : Nat} (hi : i < t) :
    (VG.Spec.Sha512.schedule M t)[i]! = VG.Spec.Sha512.W M (t - 1 - i) := by
  induction t generalizing i with
  | zero => omega
  | succ t ih =>
    rw [VG.Proof.Sha512.schedule_succ]
    cases i with
    | zero => simp
    | succ i =>
      simp only [getElem!_pos (VG.Spec.Sha512.W M t :: VG.Spec.Sha512.schedule M t) (i + 1) (by
          simp only [List.length_cons]
          have : (VG.Spec.Sha512.schedule M t).length = t := by
            clear ih hi; induction t with
            | zero => rfl
            | succ t ih => rw [VG.Proof.Sha512.schedule_succ, List.length_cons, ih]
          omega),
        List.getElem_cons_succ]
      rw [← getElem!_pos, ih (by omega)]
      congr 1; omega

theorem W_lt (M : VG.Spec.Sha512.Block) {t : Nat} (h : t < 16) : VG.Spec.Sha512.W M t = M ⟨t, h⟩ := by
  simp [VG.Spec.Sha512.W, VG.Spec.Sha512.schedule, h]

theorem W_ge (M : VG.Spec.Sha512.Block) {t : Nat} (h : 16 ≤ t) :
    VG.Spec.Sha512.W M t = VG.Spec.Sha512.ssig1 (VG.Spec.Sha512.W M (t - 2)) + VG.Spec.Sha512.W M (t - 7) + VG.Spec.Sha512.ssig0 (VG.Spec.Sha512.W M (t - 15)) + VG.Spec.Sha512.W M (t - 16) := by
  show (VG.Spec.Sha512.schedule M (t + 1)).headD 0 = _
  simp only [VG.Spec.Sha512.schedule, show ¬ t < 16 by omega, dite_false, List.headD_cons]
  rw [VG.Proof.Sha512.schedule_getElem! M (by omega), VG.Proof.Sha512.schedule_getElem! M (by omega),
    VG.Proof.Sha512.schedule_getElem! M (by omega), VG.Proof.Sha512.schedule_getElem! M (by omega),
    show t - 1 - 1 = t - 2 by omega, show t - 1 - 6 = t - 7 by omega,
    show t - 1 - 14 = t - 15 by omega, show t - 1 - 15 = t - 16 by omega]

/-! ## Rounds -/

/-- One round with explicit `Kₜ` and `Wₜ`. -/
def roundKW (v : VG.Spec.Sha512.HashValue) (k w : VG.Spec.Sha512.Word) : VG.Spec.Sha512.HashValue :=
  let a := v[0]; let b := v[1]; let c := v[2]; let d := v[3]
  let e := v[4]; let f := v[5]; let g := v[6]; let h := v[7]
  let T₁ := h + VG.Spec.Sha512.bsig1 e + VG.Spec.Sha512.ch e f g + k + w
  let T₂ := VG.Spec.Sha512.bsig0 a + VG.Spec.Sha512.maj a b c
  #v[T₁ + T₂, a, b, c, d + T₁, e, f, g]

section
variable (v : VG.Spec.Sha512.HashValue) (k w : VG.Spec.Sha512.Word)

/-! The words of `roundKW`, for rewriting the symbolic results of a round. -/

theorem roundKW_0 : (VG.Proof.Sha512.roundKW v k w)[0] =
    v[7] + VG.Spec.Sha512.bsig1 v[4] + VG.Spec.Sha512.ch v[4] v[5] v[6] + k + w + (VG.Spec.Sha512.bsig0 v[0] + VG.Spec.Sha512.maj v[0] v[1] v[2]) := rfl
theorem roundKW_1 : (VG.Proof.Sha512.roundKW v k w)[1] = v[0] := rfl
theorem roundKW_2 : (VG.Proof.Sha512.roundKW v k w)[2] = v[1] := rfl
theorem roundKW_3 : (VG.Proof.Sha512.roundKW v k w)[3] = v[2] := rfl
theorem roundKW_4 : (VG.Proof.Sha512.roundKW v k w)[4] = v[3] + (v[7] + VG.Spec.Sha512.bsig1 v[4] + VG.Spec.Sha512.ch v[4] v[5] v[6] + k + w) := rfl
theorem roundKW_5 : (VG.Proof.Sha512.roundKW v k w)[5] = v[4] := rfl
theorem roundKW_6 : (VG.Proof.Sha512.roundKW v k w)[6] = v[5] := rfl
theorem roundKW_7 : (VG.Proof.Sha512.roundKW v k w)[7] = v[6] := rfl

end

theorem round_eq (M : VG.Spec.Sha512.Block) (v : VG.Spec.Sha512.HashValue) (t : Nat) :
    VG.Spec.Sha512.round M v t = VG.Proof.Sha512.roundKW v (VG.Spec.Sha512.K t) (VG.Spec.Sha512.W M t) := rfl

theorem rounds_zero (H : VG.Spec.Sha512.HashValue) (M : VG.Spec.Sha512.Block) : VG.Spec.Sha512.rounds H M 0 = H := rfl

theorem rounds_succ (H : VG.Spec.Sha512.HashValue) (M : VG.Spec.Sha512.Block) (t : Nat) :
    VG.Spec.Sha512.rounds H M (t + 1) = VG.Spec.Sha512.round M (VG.Spec.Sha512.rounds H M t) t := by
  simp [VG.Spec.Sha512.rounds, List.range_succ, List.foldl_append]

/-! ## Bitwise identities used by the implementations -/

theorem add_left_comm {n : Nat} (a b c : BitVec n) : a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

/-- Normalizes sums (with `simp only`) up to associativity and commutativity. -/
theorem add_ac {n : Nat} : (∀ a b c : BitVec n, a + b + c = a + (b + c)) ∧
    (∀ a b : BitVec n, a + b = b + a) ∧ (∀ a b c : BitVec n, a + (b + c) = b + (a + c)) :=
  ⟨BitVec.add_assoc, BitVec.add_comm, VG.Proof.Sha512.add_left_comm⟩

/-- Bit `i` of a rotated word. -/
theorem getLsbD_rotateRight (x : VG.Spec.Sha512.Word) (r : Nat) {i : Nat} (hi : i < 64) :
    (x.rotateRight r).getLsbD i = x.getLsbD ((i + r) % 64) := by
  rw [BitVec.getLsbD_rotateRight]
  have := Nat.mod_lt r (show 64 > 0 by decide)
  split
  · exact congrArg x.getLsbD (by omega)
  · rw [decide_eq_true hi, Bool.true_and]; exact congrArg x.getLsbD (by omega)

theorem rotateRight_rotateRight (x : VG.Spec.Sha512.Word) {a b : Nat} (_hab : a + b < 64) :
    (x.rotateRight a).rotateRight b = x.rotateRight (a + b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [VG.Proof.Sha512.getLsbD_rotateRight _ _ hi, VG.Proof.Sha512.getLsbD_rotateRight _ _ (Nat.mod_lt _ (by decide)),
    VG.Proof.Sha512.getLsbD_rotateRight _ _ hi]
  exact congrArg x.getLsbD (by omega)

theorem ch_eq (x y z : VG.Spec.Sha512.Word) : VG.Spec.Sha512.ch x y z = (y ^^^ z) &&& x ^^^ z := by
  ext i; simp only [VG.Spec.Sha512.ch, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem maj_eq (x y z : VG.Spec.Sha512.Word) : VG.Spec.Sha512.maj x y z = (x ||| y) &&& z ||| x &&& y := by
  ext i; simp only [VG.Spec.Sha512.maj, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_or]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem bsig0_eq (x : VG.Spec.Sha512.Word) :
    VG.Spec.Sha512.bsig0 x = x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ (x.rotateRight 34).rotateRight 5 := by
  rw [VG.Proof.Sha512.rotateRight_rotateRight x (by omega)]; rfl

theorem bsig1_eq (x : VG.Spec.Sha512.Word) :
    VG.Spec.Sha512.bsig1 x = x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ (x.rotateRight 18).rotateRight 23 := by
  rw [VG.Proof.Sha512.rotateRight_rotateRight x (by omega)]; rfl

theorem rotateRight_xor (x y : VG.Spec.Sha512.Word) (n : Nat) :
    (x ^^^ y).rotateRight n = x.rotateRight n ^^^ y.rotateRight n := by
  ext i hi
  simp only [BitVec.getElem_rotateRight, BitVec.getElem_xor]
  split_ifs <;> rfl

theorem ssig0_eq (x : VG.Spec.Sha512.Word) :
    VG.Spec.Sha512.ssig0 x = (x.rotateRight 7 ^^^ x).rotateRight 1 ^^^ x >>> 7 := by
  rw [VG.Proof.Sha512.rotateRight_xor, VG.Proof.Sha512.rotateRight_rotateRight x (by omega), BitVec.xor_comm (x.rotateRight (7 + 1))]
  rfl

theorem ssig1_eq (x : VG.Spec.Sha512.Word) :
    VG.Spec.Sha512.ssig1 x = (x.rotateRight 42 ^^^ x).rotateRight 19 ^^^ x >>> 6 := by
  rw [VG.Proof.Sha512.rotateRight_xor, VG.Proof.Sha512.rotateRight_rotateRight x (by omega), BitVec.xor_comm (x.rotateRight (42 + 19))]
  rfl

end VG.Proof.Sha512

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha512.Shifts`. -/
section

/-!
# SHA-512: `Σ`, `σ` and `Maj` as code without rotations computes them

Without a rotation instruction, a rotation is the exclusive or of a shift each
way. The shifts of `Σ₀`, `Σ₁`, `σ₀` and `σ₁` are chained, as SIMD code computes
them: one copy of the word is shifted right by each term's amount in turn,
another left (`chain5`), and for `Σ₀` and `Σ₁` the two chains are combined
separately (`split6`). `Maj(a, b, c)` is `((a ⊕ b) ∧ (b ⊕ c)) ⊕ b`,
which lets a round reuse the previous round's `a ⊕ b` as its `b ⊕ c`.
-/

namespace VG.Proof.Sha512

open VG.Spec.Sha512 (Word bsig0 bsig1 ssig0 ssig1 maj ch)

/-- A rotation as the xor of a shift each way. -/
theorem rotateRight_eq_shifts (x : VG.Spec.Sha512.Word) {n : Nat} (h0 : 0 < n) (h : n < 64) :
    x.rotateRight n = x >>> n ^^^ x <<< (64 - n) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [VG.Proof.Sha512.getLsbD_rotateRight _ _ hi]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    decide_eq_true hi, Bool.true_and]
  by_cases hl : i < 64 - n
  · rw [Nat.mod_eq_of_lt (by omega), Nat.add_comm, decide_eq_true hl]
    simp only [Bool.not_true, Bool.false_and, Bool.xor_false]
  · rw [BitVec.getLsbD_of_ge x (n + i) (by omega), decide_eq_false hl, Bool.not_false, Bool.true_and,
      Bool.false_xor]
    exact congrArg x.getLsbD (by omega)

/-- The five terms of `σ₀` or `σ₁` as chained shifts: right by `r₁`, `r₁ + r₂`,
`r₁ + r₂ + r₃` and left by `l₁`, `l₁ + l₂`, in the order the code combines them. -/
def chain5 (x : VG.Spec.Sha512.Word) (r₁ l₁ r₂ l₂ r₃ : Nat) : VG.Spec.Sha512.Word :=
  x >>> r₁ ^^^ x <<< l₁ ^^^ x >>> r₁ >>> r₂ ^^^ x <<< l₁ <<< l₂ ^^^ x >>> r₁ >>> r₂ >>> r₃

theorem xor_left_comm (a b c : VG.Spec.Sha512.Word) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

/-- The six terms of `Σ₀` or `Σ₁` as two chains: the right shifts by `r₁`,
`r₁ + r₂`, `r₁ + r₂ + r₃` combined, the left shifts by `l₁`, `l₁ + l₂`,
`l₁ + l₂ + l₃` combined, and then the two. -/
def split6 (x : VG.Spec.Sha512.Word) (r₁ r₂ r₃ l₁ l₂ l₃ : Nat) : VG.Spec.Sha512.Word :=
  (x >>> r₁ ^^^ x >>> r₁ >>> r₂ ^^^ x >>> r₁ >>> r₂ >>> r₃) ^^^
    (x <<< l₁ ^^^ x <<< l₁ <<< l₂ ^^^ x <<< l₁ <<< l₂ <<< l₃)

theorem bsig1_split (x : VG.Spec.Sha512.Word) : VG.Proof.Sha512.split6 x 14 4 23 23 23 4 = VG.Spec.Sha512.bsig1 x := by
  simp only [VG.Proof.Sha512.split6, ← BitVec.shiftRight_add, ← BitVec.shiftLeft_add, Nat.reduceAdd]
  rw [VG.Spec.Sha512.bsig1, VG.Proof.Sha512.rotateRight_eq_shifts x (n := 14) (by decide) (by decide),
    VG.Proof.Sha512.rotateRight_eq_shifts x (n := 18) (by decide) (by decide),
    VG.Proof.Sha512.rotateRight_eq_shifts x (n := 41) (by decide) (by decide)]
  simp only [Nat.reduceSub, BitVec.xor_assoc, BitVec.xor_comm, VG.Proof.Sha512.xor_left_comm]

theorem bsig0_split (x : VG.Spec.Sha512.Word) : VG.Proof.Sha512.split6 x 28 6 5 25 5 6 = VG.Spec.Sha512.bsig0 x := by
  simp only [VG.Proof.Sha512.split6, ← BitVec.shiftRight_add, ← BitVec.shiftLeft_add, Nat.reduceAdd]
  rw [VG.Spec.Sha512.bsig0, VG.Proof.Sha512.rotateRight_eq_shifts x (n := 28) (by decide) (by decide),
    VG.Proof.Sha512.rotateRight_eq_shifts x (n := 34) (by decide) (by decide),
    VG.Proof.Sha512.rotateRight_eq_shifts x (n := 39) (by decide) (by decide)]
  simp only [Nat.reduceSub, BitVec.xor_assoc, BitVec.xor_comm, VG.Proof.Sha512.xor_left_comm]

theorem ssig1_chain (x : VG.Spec.Sha512.Word) : VG.Proof.Sha512.chain5 x 6 3 13 42 42 = VG.Spec.Sha512.ssig1 x := by
  simp only [VG.Proof.Sha512.chain5, ← BitVec.shiftRight_add, ← BitVec.shiftLeft_add, Nat.reduceAdd]
  rw [VG.Spec.Sha512.ssig1, VG.Proof.Sha512.rotateRight_eq_shifts x (n := 19) (by decide) (by decide),
    VG.Proof.Sha512.rotateRight_eq_shifts x (n := 61) (by decide) (by decide)]
  simp only [Nat.reduceSub, BitVec.xor_assoc, BitVec.xor_comm, VG.Proof.Sha512.xor_left_comm]

theorem ssig0_chain (x : VG.Spec.Sha512.Word) : VG.Proof.Sha512.chain5 x 1 56 6 7 1 = VG.Spec.Sha512.ssig0 x := by
  simp only [VG.Proof.Sha512.chain5, ← BitVec.shiftRight_add, ← BitVec.shiftLeft_add, Nat.reduceAdd]
  rw [VG.Spec.Sha512.ssig0, VG.Proof.Sha512.rotateRight_eq_shifts x (n := 1) (by decide) (by decide),
    VG.Proof.Sha512.rotateRight_eq_shifts x (n := 8) (by decide) (by decide)]
  simp only [Nat.reduceSub, BitVec.xor_assoc, BitVec.xor_comm, VG.Proof.Sha512.xor_left_comm]

theorem maj_xor (a b c : VG.Spec.Sha512.Word) : (a ^^^ b) &&& (b ^^^ c) ^^^ b = VG.Spec.Sha512.maj a b c := by
  ext i; simp only [VG.Spec.Sha512.maj, BitVec.getElem_xor, BitVec.getElem_and]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

end VG.Proof.Sha512

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha512.Word64`. -/
section

/-!
# 64-bit words as pairs of 32-bit halves

The halves (`lo`, `hi`) of sums, bitwise operations, rotations and shifts of
64-bit words, in the form 32-bit code computes them, the halves of a 64-bit
word in memory, and of the message length the padding ends with; for any
32-bit target (ARMv7, x86), whose implementations define `lo` and `hi` as
here.
-/

namespace VG.Proof.Sha512.Word64

/-- The low half of a 64-bit word. -/
def lo (x : BitVec 64) : BitVec 32 := x.extractLsb' 0 32

/-- The high half of a 64-bit word. -/
def hi (x : BitVec 64) : BitVec 32 := x.extractLsb' 32 32

/-! ## Halves -/

theorem lo_toNat (x : BitVec 64) : (VG.Proof.Sha512.Word64.lo x).toNat = x.toNat % 2 ^ 32 := by
  simp [VG.Proof.Sha512.Word64.lo]

theorem hi_toNat (x : BitVec 64) : (VG.Proof.Sha512.Word64.hi x).toNat = x.toNat / 2 ^ 32 := by
  simp only [VG.Proof.Sha512.Word64.hi, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

@[simp] theorem lo_zero : VG.Proof.Sha512.Word64.lo 0#64 = 0#32 := rfl

@[simp] theorem hi_zero : VG.Proof.Sha512.Word64.hi 0#64 = 0#32 := rfl

theorem eq_of_lo_hi {x y : BitVec 64} (h1 : VG.Proof.Sha512.Word64.lo x = VG.Proof.Sha512.Word64.lo y) (h2 : VG.Proof.Sha512.Word64.hi x = VG.Proof.Sha512.Word64.hi y) : x = y := by
  have e1 := congrArg BitVec.toNat h1
  have e2 := congrArg BitVec.toNat h2
  rw [VG.Proof.Sha512.Word64.lo_toNat, VG.Proof.Sha512.Word64.lo_toNat] at e1
  rw [VG.Proof.Sha512.Word64.hi_toNat, VG.Proof.Sha512.Word64.hi_toNat] at e2
  apply BitVec.eq_of_toNat_eq
  omega

theorem hi_append_lo (x : BitVec 64) : VG.Proof.Sha512.Word64.hi x ++ VG.Proof.Sha512.Word64.lo x = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (VG.Proof.Sha512.Word64.lo x).isLt, Nat.shiftLeft_eq, VG.Proof.Sha512.Word64.lo_toNat,
    VG.Proof.Sha512.Word64.hi_toNat]
  omega

theorem lo_append (a b : BitVec 32) : VG.Proof.Sha512.Word64.lo (a ++ b) = b := by
  simp only [VG.Proof.Sha512.Word64.lo]; exact BitVec.extractLsb'_append_eq_right

theorem hi_append (a b : BitVec 32) : VG.Proof.Sha512.Word64.hi (a ++ b) = a := by
  simp only [VG.Proof.Sha512.Word64.hi]; exact BitVec.extractLsb'_append_eq_left

/-- The carry out of the addition of the low halves (as `adds` sets it). -/
theorem lo_add (x y : BitVec 64) : VG.Proof.Sha512.Word64.lo (x + y) = VG.Proof.Sha512.Word64.lo x + VG.Proof.Sha512.Word64.lo y := by
  apply BitVec.eq_of_toNat_eq
  simp only [VG.Proof.Sha512.Word64.lo_toNat, BitVec.toNat_add]
  omega

theorem hi_add (x y : BitVec 64) :
    VG.Proof.Sha512.Word64.hi (x + y) = VG.Proof.Sha512.Word64.hi x + VG.Proof.Sha512.Word64.hi y + (if 2 ^ 32 ≤ (VG.Proof.Sha512.Word64.lo x).toNat + (VG.Proof.Sha512.Word64.lo y).toNat then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [VG.Proof.Sha512.Word64.hi_toNat, VG.Proof.Sha512.Word64.lo_toNat, BitVec.toNat_add]
  have := x.isLt; have := y.isLt
  split <;> simp <;> omega

theorem lo_xor (x y : BitVec 64) : VG.Proof.Sha512.Word64.lo (x ^^^ y) = VG.Proof.Sha512.Word64.lo x ^^^ VG.Proof.Sha512.Word64.lo y := by
  simp [VG.Proof.Sha512.Word64.lo, BitVec.extractLsb'_xor]

theorem hi_xor (x y : BitVec 64) : VG.Proof.Sha512.Word64.hi (x ^^^ y) = VG.Proof.Sha512.Word64.hi x ^^^ VG.Proof.Sha512.Word64.hi y := by
  simp [VG.Proof.Sha512.Word64.hi, BitVec.extractLsb'_xor]

theorem lo_and (x y : BitVec 64) : VG.Proof.Sha512.Word64.lo (x &&& y) = VG.Proof.Sha512.Word64.lo x &&& VG.Proof.Sha512.Word64.lo y := by
  simp [VG.Proof.Sha512.Word64.lo, BitVec.extractLsb'_and]

theorem hi_and (x y : BitVec 64) : VG.Proof.Sha512.Word64.hi (x &&& y) = VG.Proof.Sha512.Word64.hi x &&& VG.Proof.Sha512.Word64.hi y := by
  simp [VG.Proof.Sha512.Word64.hi, BitVec.extractLsb'_and]

theorem lo_or (x y : BitVec 64) : VG.Proof.Sha512.Word64.lo (x ||| y) = VG.Proof.Sha512.Word64.lo x ||| lo y := by
  simp [VG.Proof.Sha512.Word64.lo, BitVec.extractLsb'_or]

theorem hi_or (x y : BitVec 64) : VG.Proof.Sha512.Word64.hi (x ||| y) = VG.Proof.Sha512.Word64.hi x ||| hi y := by
  simp [VG.Proof.Sha512.Word64.hi, BitVec.extractLsb'_or]

/-! ## Rotations and shifts

The two parts of each half have no bits in common, so their exclusive or is
their or. -/

theorem lo_rotr {n : Nat} (x : BitVec 64) (h0 : 0 < n) (h : n < 32) :
    VG.Proof.Sha512.Word64.lo (x.rotateRight n) = VG.Proof.Sha512.Word64.lo x >>> n ^^^ VG.Proof.Sha512.Word64.hi x <<< (32 - n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [VG.Proof.Sha512.Word64.lo, VG.Proof.Sha512.Word64.hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight, BitVec.getLsbD_xor,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, Nat.mod_eq_of_lt (show n < 64 by omega)]
  by_cases hc : i < 32 - n
  · simp [hc, hi', show i < 64 - n by omega, show n + i < 32 by omega]
  · simp [hi', show i < 64 - n by omega, show ¬ n + i < 32 by omega, show ¬ i < 32 - n by omega,
      show i - (32 - n) < 32 by omega, show 32 + (i - (32 - n)) = n + i by omega]

theorem hi_rotr {n : Nat} (x : BitVec 64) (h0 : 0 < n) (h : n < 32) :
    VG.Proof.Sha512.Word64.hi (x.rotateRight n) = VG.Proof.Sha512.Word64.hi x >>> n ^^^ VG.Proof.Sha512.Word64.lo x <<< (32 - n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [VG.Proof.Sha512.Word64.lo, VG.Proof.Sha512.Word64.hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight, BitVec.getLsbD_xor,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, Nat.mod_eq_of_lt (show n < 64 by omega)]
  by_cases hc : i < 32 - n
  · simp [hc, hi', show 32 + i < 64 - n by omega, show n + i < 32 by omega,
      show n + (32 + i) = 32 + (n + i) by omega]
  · simp [show 32 + i < 64 by omega, hi', show ¬ 32 + i < 64 - n by omega,
      show ¬ n + i < 32 by omega, show ¬ i < 32 - n by omega, show i - (32 - n) < 32 by omega,
      show 32 + i - (64 - n) = i - (32 - n) by omega]

theorem lo_rotr' {n : Nat} (x : BitVec 64) (h0 : 32 < n) (h : n < 64) :
    VG.Proof.Sha512.Word64.lo (x.rotateRight n) = VG.Proof.Sha512.Word64.hi x >>> (n - 32) ^^^ VG.Proof.Sha512.Word64.lo x <<< (64 - n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [VG.Proof.Sha512.Word64.lo, VG.Proof.Sha512.Word64.hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight, BitVec.getLsbD_xor,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, Nat.mod_eq_of_lt h]
  by_cases hc : i < 64 - n
  · simp [hc, hi', show n - 32 + i < 32 by omega, show 32 + (n - 32 + i) = n + i by omega]
  · simp [show i < 64 by omega, hi', hc, show ¬ n - 32 + i < 32 by omega,
      show i - (64 - n) < 32 by omega]

theorem hi_rotr' {n : Nat} (x : BitVec 64) (h0 : 32 < n) (h : n < 64) :
    VG.Proof.Sha512.Word64.hi (x.rotateRight n) = VG.Proof.Sha512.Word64.lo x >>> (n - 32) ^^^ VG.Proof.Sha512.Word64.hi x <<< (64 - n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [VG.Proof.Sha512.Word64.lo, VG.Proof.Sha512.Word64.hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight, BitVec.getLsbD_xor,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, Nat.mod_eq_of_lt h]
  by_cases hc : i < 64 - n
  · simp [show 32 + i < 64 by omega, hc, hi', show n - 32 + i < 32 by omega,
      show ¬ 32 + i < 64 - n by omega, show 32 + i - (64 - n) = n - 32 + i by omega]
  · simp [show 32 + i < 64 by omega, hi', hc, show ¬ n - 32 + i < 32 by omega,
      show ¬ 32 + i < 64 - n by omega, show i - (64 - n) < 32 by omega,
      show 32 + i - (64 - n) = 32 + (i - (64 - n)) by omega]

theorem lo_shr {n : Nat} (x : BitVec 64) (h0 : 0 < n) (h : n < 32) :
    VG.Proof.Sha512.Word64.lo (x >>> n) = VG.Proof.Sha512.Word64.lo x >>> n ^^^ VG.Proof.Sha512.Word64.hi x <<< (32 - n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [VG.Proof.Sha512.Word64.lo, VG.Proof.Sha512.Word64.hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  by_cases hc : i < 32 - n
  · simp [hc, hi', show n + i < 32 by omega]
  · simp [hi', hc, show ¬ n + i < 32 by omega, show i - (32 - n) < 32 by omega,
      show 32 + (i - (32 - n)) = n + i by omega]

theorem hi_shr (n : Nat) (x : BitVec 64) : VG.Proof.Sha512.Word64.hi (x >>> n) = VG.Proof.Sha512.Word64.hi x >>> n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [VG.Proof.Sha512.Word64.hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight]
  by_cases hc : n + i < 32
  · simp [hi', hc, show n + (32 + i) = 32 + (n + i) by omega]
  · simp [hi', hc]
    exact BitVec.getLsbD_of_ge x _ (by omega)

/-! ## The terms of `Σ₀`, `Σ₁`, `σ₀` and `σ₁` -/

/-- A term of `Σ₀`, `Σ₁`, `σ₀` or `σ₁`. -/
inductive Term
  /-- `ROTRⁿ` (`0 < n < 64`, `n ≠ 32`) -/
  | rotr (n : Nat)
  /-- `SHRⁿ` (`0 < n < 32`) -/
  | shr (n : Nat)
  deriving DecidableEq, Repr

/-- A term's value. -/
def Term.eval (x : BitVec 64) : VG.Proof.Sha512.Word64.Term → BitVec 64
  | .rotr n => x.rotateRight n
  | .shr n => x >>> n

/-- The shift amounts that the code can encode. -/
def Term.valid : VG.Proof.Sha512.Word64.Term → Bool
  | .rotr n => 0 < n && n < 64 && n != 32
  | .shr n => 0 < n && n < 32

/-- The exclusive or of the terms. -/
def evalOps (x : BitVec 64) (ops : List VG.Proof.Sha512.Word64.Term) : BitVec 64 := ops.foldl (fun a o => a ^^^ o.eval x) 0

/-- The values of the parts of a term's low half, from the halves `L`, `H`. -/
def Term.loVals (L H : BitVec 32) : VG.Proof.Sha512.Word64.Term → List (BitVec 32)
  | .rotr n => if n < 32 then [L >>> n, H <<< (32 - n)] else [H >>> (n - 32), L <<< (64 - n)]
  | .shr n => [L >>> n, H <<< (32 - n)]

/-- The values of the parts of a term's high half. -/
def Term.hiVals (L H : BitVec 32) : VG.Proof.Sha512.Word64.Term → List (BitVec 32)
  | .rotr n => if n < 32 then [H >>> n, L <<< (32 - n)] else [L >>> (n - 32), H <<< (64 - n)]
  | .shr n => [H >>> n]

theorem Term.lo_eval {o : VG.Proof.Sha512.Word64.Term} (hv : o.valid = true) (x : BitVec 64) :
    ((o.loVals (VG.Proof.Sha512.Word64.lo x) (VG.Proof.Sha512.Word64.hi x)).foldl (· ^^^ ·) 0) = VG.Proof.Sha512.Word64.lo (o.eval x) := by
  cases o with
  | rotr n =>
    simp only [Term.valid, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hv
    simp only [Term.loVals, Term.eval]
    split
    · simp [VG.Proof.Sha512.Word64.lo_rotr x hv.1.1 (by omega)]
    · simp [VG.Proof.Sha512.Word64.lo_rotr' x (by omega) hv.1.2]
  | shr n =>
    simp only [Term.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp [Term.loVals, Term.eval, VG.Proof.Sha512.Word64.lo_shr x hv.1 hv.2]

theorem Term.hi_eval {o : VG.Proof.Sha512.Word64.Term} (hv : o.valid = true) (x : BitVec 64) :
    ((o.hiVals (VG.Proof.Sha512.Word64.lo x) (VG.Proof.Sha512.Word64.hi x)).foldl (· ^^^ ·) 0) = VG.Proof.Sha512.Word64.hi (o.eval x) := by
  cases o with
  | rotr n =>
    simp only [Term.valid, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hv
    simp only [Term.hiVals, Term.eval]
    split
    · simp [VG.Proof.Sha512.Word64.hi_rotr x hv.1.1 (by omega)]
    · simp [VG.Proof.Sha512.Word64.hi_rotr' x (by omega) hv.1.2]
  | shr n => simp [Term.hiVals, Term.eval, VG.Proof.Sha512.Word64.hi_shr]

theorem foldl_xor_acc (a : BitVec 32) (l : List (BitVec 32)) :
    l.foldl (· ^^^ ·) a = a ^^^ l.foldl (· ^^^ ·) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons]
    rw [ih, ih (0 ^^^ b)]
    simp [BitVec.xor_assoc]

theorem lo_evalOps (x : BitVec 64) (ops : List VG.Proof.Sha512.Word64.Term) (hv : ∀ o ∈ ops, o.valid = true) :
    (ops.flatMap (Term.loVals (VG.Proof.Sha512.Word64.lo x) (VG.Proof.Sha512.Word64.hi x))).foldl (· ^^^ ·) 0 = VG.Proof.Sha512.Word64.lo (VG.Proof.Sha512.Word64.evalOps x ops) := by
  suffices ∀ acc : BitVec 64, (ops.flatMap (Term.loVals (VG.Proof.Sha512.Word64.lo x) (VG.Proof.Sha512.Word64.hi x))).foldl (· ^^^ ·) (VG.Proof.Sha512.Word64.lo acc) =
      VG.Proof.Sha512.Word64.lo (ops.foldl (fun a o => a ^^^ o.eval x) acc) by
    simpa [VG.Proof.Sha512.Word64.evalOps, VG.Proof.Sha512.Word64.lo_zero] using this 0
  induction ops with
  | nil => intro; rfl
  | cons o os ih =>
    intro acc
    rw [List.flatMap_cons, List.foldl_append, List.foldl_cons,
      VG.Proof.Sha512.Word64.foldl_xor_acc (VG.Proof.Sha512.Word64.lo acc) (Term.loVals (VG.Proof.Sha512.Word64.lo x) (VG.Proof.Sha512.Word64.hi x) o), Term.lo_eval (hv o (by simp)), ← VG.Proof.Sha512.Word64.lo_xor]
    exact ih (fun o h => hv o (by simp [h])) _

theorem hi_evalOps (x : BitVec 64) (ops : List VG.Proof.Sha512.Word64.Term) (hv : ∀ o ∈ ops, o.valid = true) :
    (ops.flatMap (Term.hiVals (VG.Proof.Sha512.Word64.lo x) (VG.Proof.Sha512.Word64.hi x))).foldl (· ^^^ ·) 0 = VG.Proof.Sha512.Word64.hi (VG.Proof.Sha512.Word64.evalOps x ops) := by
  suffices ∀ acc : BitVec 64, (ops.flatMap (Term.hiVals (VG.Proof.Sha512.Word64.lo x) (VG.Proof.Sha512.Word64.hi x))).foldl (· ^^^ ·) (VG.Proof.Sha512.Word64.hi acc) =
      VG.Proof.Sha512.Word64.hi (ops.foldl (fun a o => a ^^^ o.eval x) acc) by
    simpa [VG.Proof.Sha512.Word64.evalOps, VG.Proof.Sha512.Word64.hi_zero] using this 0
  induction ops with
  | nil => intro; rfl
  | cons o os ih =>
    intro acc
    rw [List.flatMap_cons, List.foldl_append, List.foldl_cons,
      VG.Proof.Sha512.Word64.foldl_xor_acc (VG.Proof.Sha512.Word64.hi acc) (Term.hiVals (VG.Proof.Sha512.Word64.lo x) (VG.Proof.Sha512.Word64.hi x) o), Term.hi_eval (hv o (by simp)), ← VG.Proof.Sha512.Word64.hi_xor]
    exact ih (fun o h => hv o (by simp [h])) _

/-- The terms of `Σ₀`, `Σ₁`, `σ₀` and `σ₁`. -/
def bsig0 : List VG.Proof.Sha512.Word64.Term := [.rotr 28, .rotr 34, .rotr 39]
def bsig1 : List VG.Proof.Sha512.Word64.Term := [.rotr 14, .rotr 18, .rotr 41]
def ssig0 : List VG.Proof.Sha512.Word64.Term := [.rotr 1, .rotr 8, .shr 7]
def ssig1 : List VG.Proof.Sha512.Word64.Term := [.rotr 19, .rotr 61, .shr 6]

theorem bsig0_eq (x : BitVec 64) : Spec.Sha512.bsig0 x = VG.Proof.Sha512.Word64.evalOps x VG.Proof.Sha512.Word64.bsig0 := by
  simp [VG.Proof.Sha512.Word64.evalOps, VG.Proof.Sha512.Word64.bsig0, Spec.Sha512.bsig0, Term.eval]

theorem bsig1_eq (x : BitVec 64) : Spec.Sha512.bsig1 x = VG.Proof.Sha512.Word64.evalOps x VG.Proof.Sha512.Word64.bsig1 := by
  simp [VG.Proof.Sha512.Word64.evalOps, VG.Proof.Sha512.Word64.bsig1, Spec.Sha512.bsig1, Term.eval]

theorem ssig0_eq (x : BitVec 64) : Spec.Sha512.ssig0 x = VG.Proof.Sha512.Word64.evalOps x VG.Proof.Sha512.Word64.ssig0 := by
  simp [VG.Proof.Sha512.Word64.evalOps, VG.Proof.Sha512.Word64.ssig0, Spec.Sha512.ssig0, Term.eval]

theorem ssig1_eq (x : BitVec 64) : Spec.Sha512.ssig1 x = VG.Proof.Sha512.Word64.evalOps x VG.Proof.Sha512.Word64.ssig1 := by
  simp [VG.Proof.Sha512.Word64.evalOps, VG.Proof.Sha512.Word64.ssig1, Spec.Sha512.ssig1, Term.eval]

/-! ## Words in memory -/

theorem eq_of_bytes32 {x y : BitVec 32}
    (h : ∀ j < 4, x.extractLsb' (8 * j) 8 = y.extractLsb' (8 * j) 8) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e := congrArg (fun z : BitVec 8 => z.getLsbD (i % 8)) (h (i / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb'] at e
  simpa [Nat.mod_lt i (show 8 > 0 by omega), show 8 * (i / 8) + i % 8 = i by omega] using e

theorem readW_lo (m : Mem) (a : Addr) : VG.Proof.Sha512.Word64.lo (m.readW a 64) = m.readW a 32 := by
  apply VG.Proof.Sha512.Word64.eq_of_bytes32
  intro j hj
  rw [← Mem.readW_byte m a hj]
  have e := Mem.extractLsb'_read m a (n := 8) (j := j) (by omega)
  simp only [VG.Proof.Sha512.Word64.lo, Mem.readW] at e ⊢
  rw [← e]
  ext i hi
  simp [BitVec.getElem_extractLsb']
  omega

theorem readW_hi (m : Mem) (a : Addr) : VG.Proof.Sha512.Word64.hi (m.readW a 64) = m.readW (a + 4) 32 := by
  apply VG.Proof.Sha512.Word64.eq_of_bytes32
  intro j hj
  rw [← Mem.readW_byte m (a + 4) hj, show a + 4 + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (4 + j) by
    rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl]
  have e := Mem.extractLsb'_read m a (n := 8) (j := 4 + j) (by omega)
  simp only [VG.Proof.Sha512.Word64.hi, Mem.readW] at e ⊢
  rw [← e]
  ext i hi
  simp [BitVec.getElem_extractLsb', show 8 * j + i < 32 by omega,
    show 32 + (8 * j + i) = 8 * (4 + j) + i by omega]

/-- A 64-bit word in memory is its high half at `a + 4` and its low half at `a`. -/
theorem readW64 (m : Mem) (a : Addr) : m.readW a 64 = m.readW (a + 4) 32 ++ m.readW a 32 := by
  rw [← VG.Proof.Sha512.Word64.readW_lo m a, ← VG.Proof.Sha512.Word64.readW_hi m a, VG.Proof.Sha512.Word64.hi_append_lo]

/-! ## The message length -/

/-- The big-endian bytes of a 64-bit word are those of its high half, then
those of its low half. -/
theorem wordBytes_split (x : BitVec 64) :
    Spec.Sha512.wordBytes x = Spec.Sha256.wordBytes (VG.Proof.Sha512.Word64.hi x) ++ Spec.Sha256.wordBytes (VG.Proof.Sha512.Word64.lo x) := by
  simp only [Spec.Sha512.wordBytes, Spec.Sha256.wordBytes, List.range_succ, List.range_zero, List.nil_append,
    List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.cons.injEq, and_true, VG.Proof.Sha512.Word64.hi, VG.Proof.Sha512.Word64.lo]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i hi
  all_goals simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  all_goals rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega

theorem lo_shr61 (x : BitVec 64) : VG.Proof.Sha512.Word64.lo (x >>> 61) = VG.Proof.Sha512.Word64.hi x >>> 29 := by
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.Sha512.Word64.lo_toNat]
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, VG.Proof.Sha512.Word64.hi_toNat]
  have := x.isLt
  omega

theorem hi_shr61 (x : BitVec 64) : VG.Proof.Sha512.Word64.hi (x >>> 61) = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.Sha512.Word64.hi_toNat]
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (0 : BitVec 32).toNat = 0 from rfl]
  have := x.isLt
  omega

theorem lo_shl3 (x : BitVec 64) : VG.Proof.Sha512.Word64.lo (x <<< 3) = VG.Proof.Sha512.Word64.lo x <<< 3 := by
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.Sha512.Word64.lo_toNat]
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, VG.Proof.Sha512.Word64.lo_toNat]
  omega

theorem hi_shl3 (x : BitVec 64) : VG.Proof.Sha512.Word64.hi (x <<< 3) = (VG.Proof.Sha512.Word64.hi x <<< 3) ||| (VG.Proof.Sha512.Word64.lo x >>> 29) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [VG.Proof.Sha512.Word64.hi, VG.Proof.Sha512.Word64.lo, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, hi', decide_true, Bool.true_and]
  by_cases h : i < 3
  · rw [decide_eq_true (by omega : 32 + i < 64), decide_eq_false (by omega : ¬ 32 + i < 3),
      decide_eq_true (by omega : 29 + i < 32), show 32 + i - 3 = 29 + i by omega]
    rw [decide_eq_true h, Nat.zero_add]
    simp only [Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_or]
  · rw [decide_eq_true (by omega : 32 + i < 64), decide_eq_false (by omega : ¬ 32 + i < 3),
      decide_eq_true (by omega : i - 3 < 32), decide_eq_false (by omega : ¬ 29 + i < 32),
      show 32 + i - 3 = 32 + (i - 3) by omega]
    rw [decide_eq_false h]
    simp only [Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false]

end VG.Proof.Sha512.Word64

end
