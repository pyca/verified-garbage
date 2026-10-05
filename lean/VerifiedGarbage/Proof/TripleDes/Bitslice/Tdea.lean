import VerifiedGarbage.Impl.TripleDes.BitsliceLayout
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.Framework.Bitslice.Table
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.TripleDes.KeyMemory

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit`. -/
section

/-!
# The bitsliced layout's tables, as literals

The words of the bits of IP, `E`'s bits and P's destinations, each
evaluated once (`materialize_table`), from the permutations' lists: the
literals of the code that reads them (`SboxLit`, `Lit`) and the kernel's
checks of facts about them (`lit_decide`) read one number rather than walk
the permutations again.
-/

namespace VG

materialize_table Impl.TripleDes.Bitslice.ipWord 64
materialize_table Impl.TripleDes.Bitslice.eBit 48
materialize_table Impl.TripleDes.Bitslice.outBit 8 4

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Bitslice.Layout`. -/
section

/-!
# Facts about where bitsliced DES keeps each bit

Each fact is about a few small numbers, proved by evaluation.
-/

namespace VG.Proof.TripleDes.Bitslice

open VG.Spec.TripleDes VG.Impl.TripleDes.Bitslice

theorem ipWord_lt : ∀ t < 64, ipWord t < 64 := by lit_decide

theorem ipWord_inj : ∀ t < 64, ∀ u < 64, ipWord t = ipWord u → t = u := by lit_decide

theorem lWord_lt : ∀ q < 32, lWord q < 64 := by lit_decide
theorem rWord_lt : ∀ q < 32, rWord q < 64 := by lit_decide

theorem lWord_inj : ∀ q < 32, ∀ q' < 32, lWord q = lWord q' → q = q' := by lit_decide
theorem rWord_inj : ∀ q < 32, ∀ q' < 32, rWord q = rWord q' → q = q' := by lit_decide
theorem lWord_ne_rWord : ∀ q < 32, ∀ q' < 32, lWord q ≠ rWord q' := by lit_decide

/-- Every state word is a word of one of the halves. -/
theorem word_cases : ∀ w < 64, (∃ q < 32, w = lWord q) ∨ (∃ q < 32, w = rWord q) := by
  lit_decide

theorem inBit_lt : ∀ j < 8, ∀ i < 6, inBit j i < 48 := by decide

theorem eBit_lt : ∀ j < 8, ∀ i < 6, eBit (inBit j i) < 32 := by lit_decide

theorem outBit_lt : ∀ j < 8, ∀ i < 4, outBit j i < 32 := by lit_decide

/-- P sends S-box `j`'s output bit `i` to bit `outBit j i` of `f`. -/
theorem outBit_spec : ∀ j < 8, ∀ i < 4, 32 - p.getD (31 - outBit j i) 1 = 4 * (7 - j) + i := by
  lit_decide

theorem outBit_inj' : ∀ x < 32, ∀ y < 32, outBit (x / 4) (x % 4) = outBit (y / 4) (y % 4) → x = y := by
  lit_decide

theorem outBit_inj {j i j' i' : Nat} (hj : j < 8) (hi : i < 4) (hj' : j' < 8) (hi' : i' < 4)
    (h : outBit j i = outBit j' i') : j = j' ∧ i = i' := by
  have e := VG.Proof.TripleDes.Bitslice.outBit_inj' (4 * j + i) (by omega) (4 * j' + i') (by omega)
  have a : (4 * j + i) / 4 = j := by omega
  have b : (4 * j + i) % 4 = i := by omega
  have c : (4 * j' + i') / 4 = j' := by omega
  have d : (4 * j' + i') % 4 = i' := by omega
  rw [a, b, c, d] at e
  have := e h
  omega

theorem outBit_surj : ∀ q < 32, ∃ j < 8, ∃ i < 4, outBit j i = q := by lit_decide

/-- FP undoes IP: bit `i` of a block, after FP, is in the word of its IP position. -/
theorem fp_ipWord : ∀ i < 64, ipWord (64 - fp.getD (63 - i) 1) = i ^^^ 56 := by lit_decide

theorem fp_bounds : ∀ i < 64, 1 ≤ fp.getD (63 - i) 1 ∧ fp.getD (63 - i) 1 ≤ 64 := by decide +kernel
theorem ip_bounds : ∀ t < 64, 1 ≤ ip.getD (63 - t) 1 ∧ ip.getD (63 - t) 1 ≤ 64 := by decide +kernel
theorem expansion_bounds : ∀ t < 48, 1 ≤ expansion.getD (47 - t) 1 ∧ expansion.getD (47 - t) 1 ≤ 32 := by
  decide +kernel

end VG.Proof.TripleDes.Bitslice

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Bitslice.Round`. -/
section

/-!
# A bitsliced DES round, lane by lane

The state is 64 words of `w` bits (`W : Nat → BitVec w`); lane `b` of the
halves is bit `b` of their words (`half`). A round reads one half and XORs
`f` into the other (`Role`): for each S-box `j`, in order, `step` XORs its
four outputs, computed at every bit position from the words of `E` and the
round key's bits, into their words. `roundW_half` proves that a round does
in every lane what DES's round does to the halves.
-/

namespace VG.Proof.TripleDes.Bitslice

open VG.Spec.TripleDes VG.Impl.TripleDes.Bitslice VG.Bitslice VG.Proof.TripleDes

variable {w : Nat}

/-- Lane `b` of the half whose bit `q` is in the word `word q`. -/
def half (word : Nat → Nat) (W : Nat → BitVec w) (b : Nat) : BitVec 32 :=
  ofBits 32 fun q => (W (word q)).getLsbD b

/-- S-box `j`'s input in lane `b`: the words of `E` and the key's bits. -/
def sboxIn (ρ : Role) (k : BitVec 48) (j : Nat) (W : Nat → BitVec w) (b : Nat) : BitVec 6 :=
  ofBits 6 fun i => (W (readWord ρ (eBit (inBit j i)))).getLsbD b ^^ k.getLsbD (inBit j i)

/-- S-box `j`'s output bit `i`, in every lane. -/
def sboxOut (ρ : Role) (k : BitVec 48) (j : Nat) (W : Nat → BitVec w) (i : Nat) : BitVec w :=
  ofBits w fun b => (sBox j (VG.Proof.TripleDes.Bitslice.sboxIn ρ k j W b)).getLsbD i

/-- The output bit of S-box `j` that goes into the word `x`, if any. -/
def outIdx (ρ : Role) (j x : Nat) : Option Nat :=
  (List.range 4).find? fun i => writeWord ρ (outBit j i) == x

/-- S-box `j`'s step: XOR its outputs into their words. -/
def step (ρ : Role) (k : BitVec 48) (j : Nat) (W : Nat → BitVec w) : Nat → BitVec w := fun x =>
  match VG.Proof.TripleDes.Bitslice.outIdx ρ j x with
  | some i => W x ^^^ VG.Proof.TripleDes.Bitslice.sboxOut ρ k j W i
  | none => W x

/-- The first `n` S-boxes' steps. -/
def steps (ρ : Role) (k : BitVec 48) (n : Nat) (W : Nat → BitVec w) : Nat → BitVec w :=
  (List.range n).foldl (fun W j => VG.Proof.TripleDes.Bitslice.step ρ k j W) W

/-- A round. -/
def roundW (ρ : Role) (k : BitVec 48) (W : Nat → BitVec w) : Nat → BitVec w := VG.Proof.TripleDes.Bitslice.steps ρ k 8 W

theorem steps_succ (ρ : Role) (k : BitVec 48) (n : Nat) (W : Nat → BitVec w) :
    VG.Proof.TripleDes.Bitslice.steps ρ k (n + 1) W = VG.Proof.TripleDes.Bitslice.step ρ k n (VG.Proof.TripleDes.Bitslice.steps ρ k n W) := by
  simp only [VG.Proof.TripleDes.Bitslice.steps, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ## Which words a step writes -/

/-- The S-box output that is bit `q` of `f`: S-box `src q / 4`, bit `src q % 4`. -/
def src (q : Nat) : Nat := ((List.range 32).find? fun x => outBit (x / 4) (x % 4) == q).getD 0

-- The table, once, which the checks below read (`lit_decide`).
materialize_table VG.Proof.TripleDes.Bitslice.src 32

theorem src_spec : ∀ q < 32, VG.Proof.TripleDes.Bitslice.src q < 32 ∧ outBit (VG.Proof.TripleDes.Bitslice.src q / 4) (VG.Proof.TripleDes.Bitslice.src q % 4) = q := by lit_decide

theorem outIdx_read : ∀ ρ : Role, ∀ j < 8, ∀ q < 32, VG.Proof.TripleDes.Bitslice.outIdx ρ j (readWord ρ q) = none := by
  intro ρ; cases ρ <;> lit_decide

theorem outIdx_write : ∀ ρ : Role, ∀ j < 8, ∀ q < 32,
    VG.Proof.TripleDes.Bitslice.outIdx ρ j (writeWord ρ q) = if j = VG.Proof.TripleDes.Bitslice.src q / 4 then some (VG.Proof.TripleDes.Bitslice.src q % 4) else none := by
  intro ρ; cases ρ <;> lit_decide

theorem step_read (ρ : Role) (k : BitVec 48) {j q : Nat} (hj : j < 8) (hq : q < 32)
    (W : Nat → BitVec w) : VG.Proof.TripleDes.Bitslice.step ρ k j W (readWord ρ q) = W (readWord ρ q) := by
  simp only [VG.Proof.TripleDes.Bitslice.step, VG.Proof.TripleDes.Bitslice.outIdx_read ρ j hj q hq]

theorem steps_read (ρ : Role) (k : BitVec 48) {n q : Nat} (hn : n ≤ 8) (hq : q < 32)
    (W : Nat → BitVec w) : VG.Proof.TripleDes.Bitslice.steps ρ k n W (readWord ρ q) = W (readWord ρ q) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VG.Proof.TripleDes.Bitslice.steps_succ, VG.Proof.TripleDes.Bitslice.step_read ρ k (by omega) hq, ih (by omega)]

theorem sboxIn_steps (ρ : Role) (k : BitVec 48) {n j : Nat} (hn : n ≤ 8) (hj : j < 8)
    (W : Nat → BitVec w) (b : Nat) : VG.Proof.TripleDes.Bitslice.sboxIn ρ k j (VG.Proof.TripleDes.Bitslice.steps ρ k n W) b = VG.Proof.TripleDes.Bitslice.sboxIn ρ k j W b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [VG.Proof.TripleDes.Bitslice.sboxIn, getLsbD_ofBits, hi, decide_true, Bool.true_and,
    VG.Proof.TripleDes.Bitslice.steps_read ρ k hn (VG.Proof.TripleDes.Bitslice.eBit_lt j hj i hi)]

/-- After the first `n` steps, bit `b` of the word of bit `q` of the written half. -/
theorem steps_write (ρ : Role) (k : BitVec 48) {n q : Nat} (hn : n ≤ 8) (hq : q < 32)
    (W : Nat → BitVec w) (b : Nat) :
    (VG.Proof.TripleDes.Bitslice.steps ρ k n W (writeWord ρ q)).getLsbD b = ((W (writeWord ρ q)).getLsbD b ^^
      (decide (VG.Proof.TripleDes.Bitslice.src q / 4 < n) &&
        (decide (b < w) && (sBox (VG.Proof.TripleDes.Bitslice.src q / 4) (VG.Proof.TripleDes.Bitslice.sboxIn ρ k (VG.Proof.TripleDes.Bitslice.src q / 4) W b)).getLsbD (VG.Proof.TripleDes.Bitslice.src q % 4)))) := by
  induction n with
  | zero => simp [VG.Proof.TripleDes.Bitslice.steps]
  | succ n ih =>
    rw [VG.Proof.TripleDes.Bitslice.steps_succ]
    simp only [VG.Proof.TripleDes.Bitslice.step, VG.Proof.TripleDes.Bitslice.outIdx_write ρ n (by omega) q hq]
    have hs := (VG.Proof.TripleDes.Bitslice.src_spec q hq).1
    by_cases he : n = VG.Proof.TripleDes.Bitslice.src q / 4
    · subst he
      simp only [ite_true, BitVec.getLsbD_xor, ih (by omega), VG.Proof.TripleDes.Bitslice.sboxOut, getLsbD_ofBits,
        VG.Proof.TripleDes.Bitslice.sboxIn_steps ρ k (n := VG.Proof.TripleDes.Bitslice.src q / 4) (j := VG.Proof.TripleDes.Bitslice.src q / 4) (by omega) (by omega)]
      have h1 : ¬ VG.Proof.TripleDes.Bitslice.src q / 4 < VG.Proof.TripleDes.Bitslice.src q / 4 := by omega
      have h2 : VG.Proof.TripleDes.Bitslice.src q / 4 < VG.Proof.TripleDes.Bitslice.src q / 4 + 1 := by omega
      simp [h1, h2]
    · simp only [he, ite_false, ih (by omega)]
      have : (VG.Proof.TripleDes.Bitslice.src q / 4 < n + 1) ↔ (VG.Proof.TripleDes.Bitslice.src q / 4 < n) := by omega
      simp only [decide_eq_decide.mpr this]

/-! ## The round function, lane by lane -/

theorem sboxIn_eq (ρ : Role) (k : BitVec 48) {j : Nat} (hj : j < 8) (W : Nat → BitVec w)
    (b : Nat) : VG.Proof.TripleDes.Bitslice.sboxIn ρ k j W b =
      ((permute expansion (VG.Proof.TripleDes.Bitslice.half (readWord ρ) W b) ^^^ k) >>> (6 * (7 - j))).setWidth 6 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have he := VG.Proof.TripleDes.Bitslice.eBit_lt j hj i hi
  have hin := VG.Proof.TripleDes.Bitslice.inBit_lt j hj i hi
  simp only [VG.Proof.TripleDes.Bitslice.sboxIn, getLsbD_ofBits, hi, decide_true, Bool.true_and, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]
  have hidx' : 6 * (7 - j) + i = inBit j i := rfl
  simp only [hidx']
  rw [permute_bit expansion _ (by decide) _ hin]
  simp only [VG.Proof.TripleDes.Bitslice.half, getLsbD_ofBits, eBit] at he ⊢
  simp [he]

/-- Bit `q` of `f`, in lane `b`, is the output of the S-box it comes from. -/
theorem roundFunction_lane (ρ : Role) (k : BitVec 48) (W : Nat → BitVec w) (b : Nat) {q : Nat}
    (hq : q < 32) : (roundFunction (VG.Proof.TripleDes.Bitslice.half (readWord ρ) W b) k).getLsbD q =
      (sBox (VG.Proof.TripleDes.Bitslice.src q / 4) (VG.Proof.TripleDes.Bitslice.sboxIn ρ k (VG.Proof.TripleDes.Bitslice.src q / 4) W b)).getLsbD (VG.Proof.TripleDes.Bitslice.src q % 4) := by
  obtain ⟨hs, ho⟩ := VG.Proof.TripleDes.Bitslice.src_spec q hq
  have hj : VG.Proof.TripleDes.Bitslice.src q / 4 < 8 := by omega
  have hi : VG.Proof.TripleDes.Bitslice.src q % 4 < 4 := Nat.mod_lt _ (by decide)
  have spec := VG.Proof.TripleDes.Bitslice.outBit_spec _ hj _ hi
  rw [ho] at spec
  rw [roundFunction_bit _ _ q hq, VG.Proof.TripleDes.Bitslice.sboxIn_eq ρ k hj]
  simp only [spec]
  have e1 : 7 - (4 * (7 - VG.Proof.TripleDes.Bitslice.src q / 4) + VG.Proof.TripleDes.Bitslice.src q % 4) / 4 = VG.Proof.TripleDes.Bitslice.src q / 4 := by omega
  have e2 : (4 * (7 - VG.Proof.TripleDes.Bitslice.src q / 4) + VG.Proof.TripleDes.Bitslice.src q % 4) % 4 = VG.Proof.TripleDes.Bitslice.src q % 4 := by omega
  rw [e1, e2]

/-- A round XORs DES's `f` of the half it reads into the half it writes,
and leaves the half it reads, in every lane. -/
theorem roundW_half (ρ : Role) (k : BitVec 48) (W : Nat → BitVec w) {b : Nat} (hb : b < w) :
    VG.Proof.TripleDes.Bitslice.half (writeWord ρ) (VG.Proof.TripleDes.Bitslice.roundW ρ k W) b =
        VG.Proof.TripleDes.Bitslice.half (writeWord ρ) W b ^^^ roundFunction (VG.Proof.TripleDes.Bitslice.half (readWord ρ) W b) k ∧
      VG.Proof.TripleDes.Bitslice.half (readWord ρ) (VG.Proof.TripleDes.Bitslice.roundW ρ k W) b = VG.Proof.TripleDes.Bitslice.half (readWord ρ) W b := by
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro q hq
    have hj : VG.Proof.TripleDes.Bitslice.src q / 4 < 8 := by have := (VG.Proof.TripleDes.Bitslice.src_spec q hq).1; omega
    have l1 : (VG.Proof.TripleDes.Bitslice.half (writeWord ρ) (VG.Proof.TripleDes.Bitslice.roundW ρ k W) b).getLsbD q =
        (VG.Proof.TripleDes.Bitslice.roundW ρ k W (writeWord ρ q)).getLsbD b := by
      simp only [VG.Proof.TripleDes.Bitslice.half, getLsbD_ofBits, hq, decide_true, Bool.true_and]
    have l2 : (VG.Proof.TripleDes.Bitslice.half (writeWord ρ) W b).getLsbD q = (W (writeWord ρ q)).getLsbD b := by
      simp only [VG.Proof.TripleDes.Bitslice.half, getLsbD_ofBits, hq, decide_true, Bool.true_and]
    rw [BitVec.getLsbD_xor, l1, l2, VG.Proof.TripleDes.Bitslice.roundFunction_lane ρ k W b hq, VG.Proof.TripleDes.Bitslice.roundW,
      VG.Proof.TripleDes.Bitslice.steps_write ρ k (by decide) hq]
    simp [hj, hb]
  · apply BitVec.eq_of_getLsbD_eq
    intro q hq
    simp only [VG.Proof.TripleDes.Bitslice.half, getLsbD_ofBits, hq, decide_true, Bool.true_and, VG.Proof.TripleDes.Bitslice.roundW,
      VG.Proof.TripleDes.Bitslice.steps_read ρ k (n := 8) (by decide) hq]

theorem sboxIn_congr (ρ : Role) (k : BitVec 48) {j : Nat} (hj : j < 8) {W W' : Nat → BitVec w}
    (hW : ∀ x < 64, W x = W' x) (b : Nat) : VG.Proof.TripleDes.Bitslice.sboxIn ρ k j W b = VG.Proof.TripleDes.Bitslice.sboxIn ρ k j W' b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hr : readWord ρ (eBit (inBit j i)) < 64 := by
    have := VG.Proof.TripleDes.Bitslice.eBit_lt j hj i hi
    cases ρ
    · exact VG.Proof.TripleDes.Bitslice.rWord_lt _ this
    · exact VG.Proof.TripleDes.Bitslice.lWord_lt _ this
  simp only [VG.Proof.TripleDes.Bitslice.sboxIn, getLsbD_ofBits, hi, decide_true, Bool.true_and, hW _ hr]

theorem step_congr (ρ : Role) (k : BitVec 48) {j : Nat} (hj : j < 8) {W W' : Nat → BitVec w}
    (hW : ∀ y < 64, W y = W' y) {x : Nat} (hx : W x = W' x) : VG.Proof.TripleDes.Bitslice.step ρ k j W x = VG.Proof.TripleDes.Bitslice.step ρ k j W' x := by
  simp only [VG.Proof.TripleDes.Bitslice.step]
  split
  · rename_i i _
    rw [hx]
    refine congrArg (W' x ^^^ ·) ?_
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    simp only [VG.Proof.TripleDes.Bitslice.sboxOut, getLsbD_ofBits, hb, decide_true, Bool.true_and, VG.Proof.TripleDes.Bitslice.sboxIn_congr ρ k hj hW b]
  · exact hx

theorem outIdx_lt64 : ∀ ρ : Role, ∀ j < 8, ∀ x, VG.Proof.TripleDes.Bitslice.outIdx ρ j x ≠ none → x < 64 := by
  intro ρ j hj x hx
  have key : ∀ ρ : Role, ∀ j < 8, ∀ i < 4, writeWord ρ (outBit j i) < 64 := by
    intro ρ; cases ρ <;> lit_decide
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hx
  have hm := List.find?_some hi
  have hl := List.mem_range.mp (List.mem_of_find?_eq_some hi)
  simp only [beq_iff_eq] at hm
  rw [← hm]; exact key ρ j hj i hl

/-- The steps read and write only the 64 state words. -/
theorem steps_congr (ρ : Role) (k : BitVec 48) {n : Nat} (hn : n ≤ 8) {W W' : Nat → BitVec w}
    (hW : ∀ x < 64, W x = W' x) : ∀ x < 64, VG.Proof.TripleDes.Bitslice.steps ρ k n W x = VG.Proof.TripleDes.Bitslice.steps ρ k n W' x := by
  induction n with
  | zero => exact hW
  | succ n ih =>
    intro x hx
    have ih' := ih (by omega)
    rw [VG.Proof.TripleDes.Bitslice.steps_succ, VG.Proof.TripleDes.Bitslice.steps_succ]
    exact VG.Proof.TripleDes.Bitslice.step_congr ρ k (by omega) ih' (ih' x hx)

theorem steps_high (ρ : Role) (k : BitVec 48) {n : Nat} (hn : n ≤ 8) (W : Nat → BitVec w)
    {x : Nat} (hx : 64 ≤ x) : VG.Proof.TripleDes.Bitslice.steps ρ k n W x = W x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [VG.Proof.TripleDes.Bitslice.steps_succ]
    have : VG.Proof.TripleDes.Bitslice.outIdx ρ n x = none := by
      cases h : VG.Proof.TripleDes.Bitslice.outIdx ρ n x with
      | none => rfl
      | some i =>
        have := VG.Proof.TripleDes.Bitslice.outIdx_lt64 ρ n (by omega) x (by rw [h]; exact Option.some_ne_none i)
        omega
    simp only [VG.Proof.TripleDes.Bitslice.step, this, ih (by omega)]

/-- The words of neither half are left alone. -/
theorem roundW_other (ρ : Role) (k : BitVec 48) (W : Nat → BitVec w) {x : Nat}
    (hx : ∀ q < 32, x ≠ writeWord ρ q) : VG.Proof.TripleDes.Bitslice.roundW ρ k W x = W x := by
  have key : ∀ n ≤ 8, VG.Proof.TripleDes.Bitslice.steps ρ k n W x = W x := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [VG.Proof.TripleDes.Bitslice.steps_succ]
      have : VG.Proof.TripleDes.Bitslice.outIdx ρ n x = none := by
        unfold VG.Proof.TripleDes.Bitslice.outIdx
        rw [List.find?_eq_none]
        intro i hi
        simp only [List.mem_range] at hi
        have := hx (outBit n i) (VG.Proof.TripleDes.Bitslice.outBit_lt n (by omega) i hi)
        simp [Ne.symm this]
      simp only [VG.Proof.TripleDes.Bitslice.step, this, ih (by omega)]
  exact key 8 (Nat.le_refl _)

end VG.Proof.TripleDes.Bitslice

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Bitslice.Pass`. -/
section

/-!
# A bitsliced DES pass, lane by lane

Lane `b` of the state is the 64-bit value `ipLane W b`: the left half, then
the right half. A pass is eight pairs of rounds, the first reading the
right half and the second the left (`pairs`), so that no word moves, and
then the exchange of the halves (`swapW`): `pass_lane` proves that it does
in every lane what `desCore` (DES between IP and FP) does.
-/

namespace VG.Proof.TripleDes.Bitslice

open VG.Spec.TripleDes VG.Impl.TripleDes.Bitslice VG.Bitslice VG.Proof.TripleDes

variable {w : Nat}

/-- Lane `b`: the left half, then the right half. -/
def ipLane (W : Nat → BitVec w) (b : Nat) : BitVec 64 := VG.Proof.TripleDes.Bitslice.half lWord W b ++ VG.Proof.TripleDes.Bitslice.half rWord W b

/-- The first `n` pairs of rounds, with the key of round `r` (from 0) `key r`. -/
def pairs (key : Nat → BitVec 48) : Nat → (Nat → BitVec w) → Nat → BitVec w
  | 0, W => W
  | n + 1, W => VG.Proof.TripleDes.Bitslice.roundW .ab (key (2 * n + 1)) (VG.Proof.TripleDes.Bitslice.roundW .ba (key (2 * n)) (VG.Proof.TripleDes.Bitslice.pairs key n W))

/-- The word of the other half's same bit, for the words of the halves. -/
def partner (x : Nat) : Option Nat :=
  match (List.range 32).find? (fun q => lWord q == x) with
  | some q => some (rWord q)
  | none => ((List.range 32).find? (fun q => rWord q == x)).map lWord

-- The table, once, which the checks below and the targets' read (`lit_decide`).
materialize_table VG.Proof.TripleDes.Bitslice.partner 128

/-- Exchange the halves. -/
def swapW (W : Nat → BitVec w) : Nat → BitVec w := fun x =>
  match VG.Proof.TripleDes.Bitslice.partner x with
  | some y => W y
  | none => W x

theorem partner_l : ∀ q < 32, VG.Proof.TripleDes.Bitslice.partner (lWord q) = some (rWord q) := by lit_decide
theorem partner_r : ∀ q < 32, VG.Proof.TripleDes.Bitslice.partner (rWord q) = some (lWord q) := by lit_decide

theorem swapW_half_l (W : Nat → BitVec w) (b : Nat) : VG.Proof.TripleDes.Bitslice.half lWord (VG.Proof.TripleDes.Bitslice.swapW W) b = VG.Proof.TripleDes.Bitslice.half rWord W b := by
  apply BitVec.eq_of_getLsbD_eq
  intro q hq
  simp only [VG.Proof.TripleDes.Bitslice.half, getLsbD_ofBits, hq, decide_true, Bool.true_and, VG.Proof.TripleDes.Bitslice.swapW, VG.Proof.TripleDes.Bitslice.partner_l q hq]

theorem swapW_half_r (W : Nat → BitVec w) (b : Nat) : VG.Proof.TripleDes.Bitslice.half rWord (VG.Proof.TripleDes.Bitslice.swapW W) b = VG.Proof.TripleDes.Bitslice.half lWord W b := by
  apply BitVec.eq_of_getLsbD_eq
  intro q hq
  simp only [VG.Proof.TripleDes.Bitslice.half, getLsbD_ofBits, hq, decide_true, Bool.true_and, VG.Proof.TripleDes.Bitslice.swapW, VG.Proof.TripleDes.Bitslice.partner_r q hq]

theorem readWord_ba : readWord .ba = rWord := rfl
theorem readWord_ab : readWord .ab = lWord := rfl
theorem writeWord_ba : writeWord .ba = lWord := rfl
theorem writeWord_ab : writeWord .ab = rWord := rfl

/-- `n` pairs of rounds are `2 n` Feistel steps, in every lane. -/
theorem pairs_halves (keys : DesSchedule) (d : Direction) (n : Nat) (W : Nat → BitVec w)
    {b : Nat} (hb : b < w) :
    (VG.Proof.TripleDes.Bitslice.half lWord (VG.Proof.TripleDes.Bitslice.pairs (roundKey keys d) n W) b, VG.Proof.TripleDes.Bitslice.half rWord (VG.Proof.TripleDes.Bitslice.pairs (roundKey keys d) n W) b) =
      roundPrefix keys d (2 * n) (VG.Proof.TripleDes.Bitslice.half lWord W b, VG.Proof.TripleDes.Bitslice.half rWord W b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [e, roundPrefix_succ, roundPrefix_succ, ← ih]
    simp only [VG.Proof.TripleDes.Bitslice.pairs]
    obtain ⟨ba₁, ba₂⟩ := VG.Proof.TripleDes.Bitslice.roundW_half .ba (roundKey keys d (2 * n)) (VG.Proof.TripleDes.Bitslice.pairs (roundKey keys d) n W) hb
    obtain ⟨ab₁, ab₂⟩ := VG.Proof.TripleDes.Bitslice.roundW_half .ab (roundKey keys d (2 * n + 1))
      (VG.Proof.TripleDes.Bitslice.roundW .ba (roundKey keys d (2 * n)) (VG.Proof.TripleDes.Bitslice.pairs (roundKey keys d) n W)) hb
    simp only [VG.Proof.TripleDes.Bitslice.readWord_ba, VG.Proof.TripleDes.Bitslice.readWord_ab, VG.Proof.TripleDes.Bitslice.writeWord_ba, VG.Proof.TripleDes.Bitslice.writeWord_ab] at ab₁ ab₂ ba₁ ba₂
    simp only [feistelStep]
    rw [ab₁, ab₂, ba₁, ba₂]

theorem ipLane_hi (W : Nat → BitVec w) (b : Nat) :
    ((VG.Proof.TripleDes.Bitslice.ipLane W b >>> 32).setWidth 32) = VG.Proof.TripleDes.Bitslice.half lWord W b := appended_left _ _

theorem ipLane_lo (W : Nat → BitVec w) (b : Nat) : (VG.Proof.TripleDes.Bitslice.ipLane W b).setWidth 32 = VG.Proof.TripleDes.Bitslice.half rWord W b :=
  appended_right _ _

/-- A pass: eight pairs of rounds, then the exchange of the halves. -/
def passW (keys : DesSchedule) (d : Direction) (W : Nat → BitVec w) : Nat → BitVec w :=
  VG.Proof.TripleDes.Bitslice.swapW (VG.Proof.TripleDes.Bitslice.pairs (roundKey keys d) 8 W)

theorem pass_lane (keys : DesSchedule) (d : Direction) (W : Nat → BitVec w) {b : Nat}
    (hb : b < w) : VG.Proof.TripleDes.Bitslice.ipLane (VG.Proof.TripleDes.Bitslice.passW keys d W) b = desCore keys d (VG.Proof.TripleDes.Bitslice.ipLane W b) := by
  rw [desCore_roundPrefix]
  simp only [VG.Proof.TripleDes.Bitslice.ipLane_hi, VG.Proof.TripleDes.Bitslice.ipLane_lo]
  rw [← VG.Proof.TripleDes.Bitslice.pairs_halves keys d 8 W hb]
  simp only [VG.Proof.TripleDes.Bitslice.ipLane, VG.Proof.TripleDes.Bitslice.passW, VG.Proof.TripleDes.Bitslice.swapW_half_l, VG.Proof.TripleDes.Bitslice.swapW_half_r]

end VG.Proof.TripleDes.Bitslice

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Bitslice.Io`. -/
section

/-!
# Into and out of the bitsliced state, for 64 blocks

64 blocks, as little-endian 64-bit words, are transposed (`transposeW`) so
that word `j` holds bit `j` of every block. Lane `b` of the state is then
IP of block `b` (`ipLane_transpose`), and transposing a state back gives,
in each lane, the little-endian word of FP of its value (`transpose_out`).
-/

namespace VG.Proof.TripleDes.Bitslice

open VG.Spec.TripleDes VG.Impl.TripleDes.Bitslice VG.Bitslice VG.Proof.TripleDes

/-- Bit `b` of word `j` is bit `j` of word `b`. -/
def transposeW (W : Nat → BitVec 64) : Nat → BitVec 64 := fun j => ofBits 64 fun b => (W b).getLsbD j

theorem ipLane_bit {w : Nat} (W : Nat → BitVec w) (b : Nat) {t : Nat} (ht : t < 64) :
    (VG.Proof.TripleDes.Bitslice.ipLane W b).getLsbD t = (W (ipWord t)).getLsbD b := by
  simp only [VG.Proof.TripleDes.Bitslice.ipLane, BitVec.getLsbD_append]
  by_cases h : t < 32
  · simp only [h, ite_true, VG.Proof.TripleDes.Bitslice.half, getLsbD_ofBits, decide_true, Bool.true_and, rWord]
  · have h' : t - 32 < 32 := by omega
    simp only [h, ite_false, VG.Proof.TripleDes.Bitslice.half, getLsbD_ofBits, h', decide_true, Bool.true_and, lWord]
    congr 3
    omega

theorem xor56_xor56 (a : Nat) : a ^^^ 56 ^^^ 56 = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- After transposing 64 little-endian blocks, lane `b` is IP of block `b`. -/
theorem ipLane_transpose (W : Nat → BitVec 64) (x : BitVec 64) {b : Nat} (hb : b < 64)
    (hW : ∀ j < 64, (W b).getLsbD j = x.getLsbD (j ^^^ 56)) :
    VG.Proof.TripleDes.Bitslice.ipLane (VG.Proof.TripleDes.Bitslice.transposeW W) b = permute ip x := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have hw := VG.Proof.TripleDes.Bitslice.ipWord_lt t ht
  rw [VG.Proof.TripleDes.Bitslice.ipLane_bit _ _ ht, permute_bit ip x (by decide) t ht]
  simp only [VG.Proof.TripleDes.Bitslice.transposeW, getLsbD_ofBits, hb, decide_true, Bool.true_and, hW _ hw]
  simp only [ipWord, VG.Proof.TripleDes.Bitslice.xor56_xor56]

/-- Transposing back: in each lane, the little-endian word of FP of its value. -/
theorem transpose_out (W : Nat → BitVec 64) (b : Nat) :
    ∀ j < 64, (VG.Proof.TripleDes.Bitslice.transposeW W b).getLsbD j = (permute fp (VG.Proof.TripleDes.Bitslice.ipLane W b)).getLsbD (j ^^^ 56) := by
  intro j hj
  have hj' : j ^^^ 56 < 64 := Nat.xor_lt_two_pow (n := 6) hj (by decide)
  obtain ⟨lo, hi⟩ := VG.Proof.TripleDes.Bitslice.fp_bounds _ hj'
  have ht : 64 - fp.getD (63 - (j ^^^ 56)) 1 < 64 := by omega
  rw [permute_bit fp _ (by decide) _ hj', VG.Proof.TripleDes.Bitslice.ipLane_bit _ _ ht, VG.Proof.TripleDes.Bitslice.fp_ipWord _ hj', VG.Proof.TripleDes.Bitslice.xor56_xor56]
  simp only [VG.Proof.TripleDes.Bitslice.transposeW, getLsbD_ofBits, hj, decide_true, Bool.true_and]

end VG.Proof.TripleDes.Bitslice

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea`. -/
section

/-!
# Three bitsliced DES passes, and the blocks they come from

Target-independent facts for bitsliced TDEA on `w`-bit words: the state
words a round, pairs of rounds and a pass compute depend only on the 64
state words (`*_congr`); TDEA's three passes (`tdeaW`) do in every lane
what TDEA does between IP and FP (`tdeaW_lane`); and ECB's result is that
of each of its blocks (`ecb_blocks`).
-/

namespace VG.Proof.TripleDes.Bitslice

open VG VG.Spec.TripleDes VG.Impl.TripleDes.Bitslice VG.Proof.TripleDes

variable {w : Nat}

theorem roundW_congr (ρ : Role) (k : BitVec 48) {W W' : Nat → BitVec w}
    (hW : ∀ x < 64, W x = W' x) : ∀ x < 64, VG.Proof.TripleDes.Bitslice.roundW ρ k W x = VG.Proof.TripleDes.Bitslice.roundW ρ k W' x :=
  VG.Proof.TripleDes.Bitslice.steps_congr ρ k (Nat.le_refl 8) hW

theorem pairs_congr (key : Nat → BitVec 48) (n : Nat) {W W' : Nat → BitVec w}
    (hW : ∀ x < 64, W x = W' x) : ∀ x < 64, VG.Proof.TripleDes.Bitslice.pairs key n W x = VG.Proof.TripleDes.Bitslice.pairs key n W' x := by
  induction n with
  | zero => exact hW
  | succ n ih =>
    intro x hx
    simp only [VG.Proof.TripleDes.Bitslice.pairs]
    exact VG.Proof.TripleDes.Bitslice.roundW_congr .ab _ (VG.Proof.TripleDes.Bitslice.roundW_congr .ba _ ih) x hx

theorem pairs_keys_congr {key key' : Nat → BitVec 48} (n : Nat)
    (hk : ∀ r < 2 * n, key r = key' r) (W : Nat → BitVec w) : VG.Proof.TripleDes.Bitslice.pairs key n W = VG.Proof.TripleDes.Bitslice.pairs key' n W := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [VG.Proof.TripleDes.Bitslice.pairs]
    rw [ih (fun r hr => hk r (by omega)), hk (2 * n) (by omega), hk (2 * n + 1) (by omega)]

theorem partner_lt : ∀ k < 128, ∀ y, VG.Proof.TripleDes.Bitslice.partner k = some y → y < 64 := by
  intro k hk y h
  have key : ∀ k < 128, (VG.Proof.TripleDes.Bitslice.partner k).all (· < 64) = true := by lit_decide
  have := key k hk
  rw [h] at this
  simpa using this

theorem swapW_congr {W W' : Nat → BitVec w} (hW : ∀ y < 64, W y = W' y) :
    ∀ x < 64, VG.Proof.TripleDes.Bitslice.swapW W x = VG.Proof.TripleDes.Bitslice.swapW W' x := by
  intro x hx
  simp only [VG.Proof.TripleDes.Bitslice.swapW]
  rcases hp : VG.Proof.TripleDes.Bitslice.partner x with _ | y
  · exact hW x hx
  · exact hW y (VG.Proof.TripleDes.Bitslice.partner_lt x (by omega) y hp)

theorem passW_congr (keys : DesSchedule) (d : Direction) {W W' : Nat → BitVec w}
    (hW : ∀ y < 64, W y = W' y) : ∀ x < 64, VG.Proof.TripleDes.Bitslice.passW keys d W x = VG.Proof.TripleDes.Bitslice.passW keys d W' x :=
  VG.Proof.TripleDes.Bitslice.swapW_congr (VG.Proof.TripleDes.Bitslice.pairs_congr _ 8 hW)

theorem ipLane_congr {W W' : Nat → BitVec w} (hW : ∀ x < 64, W x = W' x) (b : Nat) :
    VG.Proof.TripleDes.Bitslice.ipLane W b = VG.Proof.TripleDes.Bitslice.ipLane W' b := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  rw [VG.Proof.TripleDes.Bitslice.ipLane_bit _ _ ht, VG.Proof.TripleDes.Bitslice.ipLane_bit _ _ ht, hW _ (VG.Proof.TripleDes.Bitslice.ipWord_lt t ht)]

/-! ## TDEA -/

/-- TDEA's three passes with the schedule `K`, in the direction `d`. -/
def tdeaW (K : Schedule) : Direction → (Nat → BitVec w) → Nat → BitVec w
  | .encrypt, W => VG.Proof.TripleDes.Bitslice.passW (componentSchedule K 2) .encrypt
      (VG.Proof.TripleDes.Bitslice.passW (componentSchedule K 1) .decrypt (VG.Proof.TripleDes.Bitslice.passW (componentSchedule K 0) .encrypt W))
  | .decrypt, W => VG.Proof.TripleDes.Bitslice.passW (componentSchedule K 0) .decrypt
      (VG.Proof.TripleDes.Bitslice.passW (componentSchedule K 1) .encrypt (VG.Proof.TripleDes.Bitslice.passW (componentSchedule K 2) .decrypt W))

/-- What ECB does to one block. -/
def blockOut (K : Schedule) : Direction → Block → Block
  | .encrypt => encryptBlock K
  | .decrypt => decryptBlock K

/-- The three DES cores of TDEA, between IP and FP. -/
def cores (K : Schedule) : Direction → BitVec 64 → BitVec 64
  | .encrypt, x => desCore (componentSchedule K 2) .encrypt
      (desCore (componentSchedule K 1) .decrypt (desCore (componentSchedule K 0) .encrypt x))
  | .decrypt, x => desCore (componentSchedule K 0) .decrypt
      (desCore (componentSchedule K 1) .encrypt (desCore (componentSchedule K 2) .decrypt x))

theorem tdeaW_lane (K : Schedule) (d : Direction) (W : Nat → BitVec w) {b : Nat} (hb : b < w) :
    VG.Proof.TripleDes.Bitslice.ipLane (VG.Proof.TripleDes.Bitslice.tdeaW K d W) b = VG.Proof.TripleDes.Bitslice.cores K d (VG.Proof.TripleDes.Bitslice.ipLane W b) := by
  cases d <;> simp only [VG.Proof.TripleDes.Bitslice.tdeaW, VG.Proof.TripleDes.Bitslice.cores, VG.Proof.TripleDes.Bitslice.pass_lane _ _ _ hb]

theorem blockOut_cores (K : Schedule) (d : Direction) (B : Block) :
    VG.Proof.TripleDes.Bitslice.blockOut K d B = encodeBlock (permute fp (VG.Proof.TripleDes.Bitslice.cores K d (permute ip (decodeBlock B)))) := by
  cases d
  · exact encryptBlock_eq_cores K B
  · exact decryptBlock_eq_cores K B

/-! ## Blocks in memory -/

/-- Block `i` of the data at `p`. -/
abbrev wAt (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (8 * i)

theorem wAt_wAt (D : Addr) (a i : Nat) : VG.Proof.TripleDes.Bitslice.wAt (VG.Proof.TripleDes.Bitslice.wAt D a) i = VG.Proof.TripleDes.Bitslice.wAt D (a + i) := by
  simp only [VG.Proof.TripleDes.Bitslice.wAt, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2; omega

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 8⟩) hd (by show 8 ≤ 2 ^ 64; decide) hi

theorem toNat_ofNat_of_le {m n : Nat} (hm : m ≤ n) (hn : 8 * n ≤ 2 ^ 64) :
    (BitVec.ofNat 64 m).toNat = m := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem ecb_blocks (K : Schedule) (d : Direction) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, blockAt m' (VG.Proof.TripleDes.Bitslice.wAt D b) = VG.Proof.TripleDes.Bitslice.blockOut K d (blockAt m (VG.Proof.TripleDes.Bitslice.wAt D b))) :
    blocksAt m' D n = Spec.TripleDes.ecb K d (blocksAt m D n) := by
  simp only [blocksAt, Spec.TripleDes.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  exact h b (List.mem_range.mp hb)

end VG.Proof.TripleDes.Bitslice

end
