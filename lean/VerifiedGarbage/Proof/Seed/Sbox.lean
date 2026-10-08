import VerifiedGarbage.Spec.Seed
import VerifiedGarbage.Impl.Seed.Layers
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Seed.SboxLit

/-!
# SEED's S-boxes through the AES S-box

`s0_eq` and `s1_eq`: `S0(x) = P0(S_AES(M x)) ⊕ 0xE7` and
`S1(x) = P1(S_AES(M x)) ⊕ 0x2B` (`Impl/Seed/Layers.lean`), for every byte
`x`. As in `Proof/Aes/SboxSpec.lean`, the kernel evaluates both sides on
truth tables of the 256 inputs at once (`sboxes_table`), and `row` reads
off each input.
-/

namespace VG.Proof.Seed

open VG VG.Bitslice VG.Proof.Aes VG.Impl.Seed

/-- The XOR of the bits `l` of `b`. -/
def xorOf (b : Byte) (l : List Nat) : Bool := l.foldr (fun i acc => b.getLsbD i ^^ acc) false

@[simp] theorem xorOf_nil (b : Byte) : xorOf b [] = false := rfl

@[simp] theorem xorOf_cons (b : Byte) (i : Nat) (l : List Nat) :
    xorOf b (i :: l) = (b.getLsbD i ^^ xorOf b l) := rfl

/-- The linear map with the rows `rows`: bit `j` is the XOR of the bits
`rows[j]` of `b`. -/
def linB (rows : List (List Nat)) (b : Byte) : Byte := ofBits 8 fun j => xorOf b (rows.getD j [])

theorem getLsbD_linB (rows : List (List Nat)) (b : Byte) {j : Nat} (hj : j < 8) :
    (linB rows b).getLsbD j = xorOf b (rows.getD j []) := by
  simp only [linB, getLsbD_ofBits, hj, decide_true, Bool.true_and]

/-! ## Truth tables -/

/-- The XOR of the tables `l` of `A`. -/
def xorOfT (A : List Nat) (l : List Nat) : Nat := l.foldr (fun i acc => A.getD i 0 ^^^ acc) 0

def linT (rows : List (List Nat)) (A : List Nat) : List Nat :=
  (List.range 8).map fun j => xorOfT A (rows.getD j [])

/-- The tables `A`, XORed with the constant `c` on every input. -/
def xorConstT (A : List Nat) (c : Byte) : List Nat :=
  (List.range 8).map fun j => A.getD j 0 ^^^ (if c.getLsbD j then ONES else 0)

theorem testBit_xorOfT (A : List Nat) (c : Nat) {l : List Nat} (hl : ∀ i ∈ l, i < 8) :
    (xorOfT A l).testBit c = xorOf (row A c) l := by
  induction l with
  | nil => simp [xorOfT, xorOf]
  | cons i l ih =>
    have hi := hl i List.mem_cons_self
    simp only [xorOfT, List.foldr_cons, Nat.testBit_xor, xorOf_cons] at ih ⊢
    rw [ih fun i h => hl i (List.mem_cons_of_mem _ h), getLsbD_row _ _ hi]

theorem row_linT {rows : List (List Nat)} (hr : ∀ l ∈ rows, ∀ i ∈ l, i < 8) (A : List Nat)
    (c : Nat) : row (linT rows A) c = linB rows (row A c) := by
  refine row_ext fun j hj => ?_
  rw [getLsbD_linB _ _ hj]
  simp only [linT, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some]
  simp only [← List.getD_eq_getElem?_getD]
  refine testBit_xorOfT A c fun i h => ?_
  by_cases hj' : j < rows.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some] at h
    exact hr _ (List.getElem_mem hj') i h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none] at h
    cases h

theorem row_xorConstT (A : List Nat) (b : Byte) {c : Nat} (hc : c < 256) :
    row (xorConstT A b) c = row A c ^^^ b := by
  refine row_ext fun j hj => ?_
  simp only [BitVec.getLsbD_xor, getLsbD_row _ _ hj]
  simp only [xorConstT, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, Nat.testBit_xor, testBit_ite_ONES, hc, decide_true,
    Bool.and_true]

/-- The truth table of bit `k` of the input. -/
def inT (k : Nat) : Nat := tableOf (fun c => c.testBit k) 256

def inTs : List Nat := (List.range 8).map inT

theorem row_inTs {c : Nat} (hc : c < 256) : row inTs c = BitVec.ofNat 8 c := by
  refine row_ext fun j hj => ?_
  simp only [inTs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
    BitVec.getLsbD_ofNat, hj]

/-- The truth tables of the S-box `odd`, from the packed table. -/
def tableT (odd : Bool) : List Nat :=
  (List.range 8).map fun j => tableOf (fun c => (sNat odd c).testBit j) 256

theorem row_tableT (odd : Bool) {c : Nat} (hc : c < 256) : row (tableT odd) c = (sTable odd).getD c 0 := by
  refine row_ext fun j hj => ?_
  rw [sTable_getD, BitVec.getLsbD_ofNat]
  simp only [tableT, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, testBit_tableOf, hc, decide_true, Bool.true_and, hj]

/-! ## The S-boxes -/

theorem rows_lt : ∀ rows ∈ [mRows, p0Rows, p1Rows], ∀ l ∈ rows, ∀ i ∈ l, i < 8 := by decide

theorem sboxes_table : ∀ odd ∈ [false, true],
    xorConstT (linT (pRows odd) (sboxT (linT mRows inTs))) (sConst odd) = tableT odd := by
  lit_decide

/-- SEED's S-boxes through AES's. -/
theorem sbox_eq (odd : Bool) (b : Byte) :
    (sTable odd).getD b.toNat 0 =
      linB (pRows odd) (Spec.Aes.sbox (linB mRows b)) ^^^ sConst odd := by
  have hc := b.isLt
  have hp : ∀ l ∈ pRows odd, ∀ i ∈ l, i < 8 := by
    cases odd
    · exact rows_lt p0Rows (by simp)
    · exact rows_lt p1Rows (by simp)
  have h := congrArg (row · b.toNat) (sboxes_table odd (by cases odd <;> simp))
  rw [row_tableT _ hc, row_xorConstT _ _ hc, row_linT hp, row_sboxT (by simp [linT]) hc,
    row_linT (rows_lt mRows (by simp)), row_inTs hc, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  exact h.symm

theorem s0_eq (b : Byte) :
    Spec.Seed.s0.getD b.toNat 0 = linB p0Rows (Spec.Aes.sbox (linB mRows b)) ^^^ 0xE7 :=
  sbox_eq false b

theorem s1_eq (b : Byte) :
    Spec.Seed.s1.getD b.toNat 0 = linB p1Rows (Spec.Aes.sbox (linB mRows b)) ^^^ 0x2B :=
  sbox_eq true b

end VG.Proof.Seed
