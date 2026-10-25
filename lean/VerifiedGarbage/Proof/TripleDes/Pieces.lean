module

public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.Proof.Framework.Bitslice.Table
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.Round

/-!
# A DES round, one S-box at a time

The code of every target that runs the S-boxes one at a time (on PPC64LE
and RISC-V) forms the six input bits of S-box `i` (`roundChunk i`, of E of R
XORed with the round key) and XORs its four output bits into L at their
destinations under P (`boxPiece i`); the eight pieces XOR to the round
function (`contributions_roundFunction`). Untrusted.
-/

@[expose] public section

namespace VG.Proof.TripleDes

open VG.Bitslice VG.Spec.TripleDes

def roundChunk (i : Nat) (r : BitVec 32) (k : BitVec 48) : BitVec 6 :=
  ((permute expansion r ^^^ k) >>> (6 * (7 - i))).setWidth 6

theorem roundChunk_bit (i j : Nat) (hi : i < 8) (hj : j < 6)
    (r : BitVec 64) (k : BitVec 64) :
    (roundChunk i (r.setWidth 32) (k.setWidth 48)).getLsbD j =
      (r.getLsbD (32 - expansion.getD (6 * i + 5 - j) 1) ^^
        k.getLsbD (47 - (6 * i + 5 - j))) := by
  have ht : 6 * (7 - i) + j < 48 := by omega
  have heq : 48 - 1 - (6 * (7 - i) + j) = 6 * i + 5 - j := by omega
  have hkey : 6 * (7 - i) + j = 47 - (6 * i + 5 - j) := by omega
  have hsource : 32 - expansion.getD (6 * i + 5 - j) 1 < 32 := by
    have hb : ∀ t < 48, 1 ≤ expansion.getD t 1 := by decide +kernel
    have hpos : 6 * i + 5 - j < 48 := by omega
    have := hb _ hpos
    omega
  simp only [roundChunk, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]
  rw [permute_bit _ _ (by decide) _ ht]
  rw [heq]
  simp only [BitVec.getLsbD_setWidth, hsource, ht, decide_true, Bool.true_and]
  rw [hkey]

def boxSource (q : Nat) : Nat := p.getD (31 - q) 1 - 1

def boxPiece (i : Nat) (b : BitVec 4) : BitVec 32 :=
  ofBits 32 fun q => if boxSource q / 4 = i then
    b.getLsbD (3 - boxSource q % 4) else false

theorem boxSource_shape : ∀ j < 32,
    7 - (32 - p.getD (31 - j) 1) / 4 = boxSource j / 4 ∧
    (32 - p.getD (31 - j) 1) % 4 = 3 - boxSource j % 4 ∧
    boxSource j / 4 < 8 := by
  decide +kernel

theorem boxPiece_round_bit (i : Nat) (r : BitVec 32) (k : BitVec 48)
    (j : Nat) (hj : j < 32) :
    (boxPiece i (sBox i (roundChunk i r k))).getLsbD j =
      if boxSource j / 4 = i then (roundFunction r k).getLsbD j else false := by
  simp only [boxPiece, getLsbD_ofBits, hj, decide_true, Bool.true_and]
  by_cases heq : boxSource j / 4 = i
  · simp only [heq, ite_true]
    rw [roundFunction_bit r k j hj]
    obtain ⟨hidx, hbit, _⟩ := boxSource_shape j hj
    simp only [hidx, hbit, heq, roundChunk]
  · simp only [heq, ite_false]

theorem foldl_xor_bits (xs : List Nat) (f : Nat → BitVec 32) (a : BitVec 32) (j : Nat) :
    (xs.foldl (fun out i => out ^^^ f i) a).getLsbD j =
      xs.foldl (fun out i => out ^^ (f i).getLsbD j) (a.getLsbD j) := by
  induction xs generalizing a with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.foldl_cons, ih, BitVec.getLsbD_xor]

theorem select_xor : ∀ n < 8, ∀ b : Bool,
    (List.range 8).foldl (fun out i => out ^^ (if n = i then b else false)) false = b := by
  decide +kernel

/-- The eight S-box contributions give the standard DES round function. -/
theorem boxPieces_eq_roundFunction (r : BitVec 32) (k : BitVec 48) :
    (List.range 8).foldl (fun out i => out ^^^ boxPiece i (sBox i (roundChunk i r k)))
      (0 : BitVec 32) = roundFunction r k := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hfold : (fun (out : Bool) i => out ^^
      (boxPiece i (sBox i (roundChunk i r k))).getLsbD j) =
      (fun out i => out ^^ (if boxSource j / 4 = i then
        (roundFunction r k).getLsbD j else false)) := by
    funext out i
    exact congrArg (fun b => out ^^ b) (boxPiece_round_bit i r k j hj)
  have hbits := foldl_xor_bits (List.range 8)
    (fun i => boxPiece i (sBox i (roundChunk i r k))) 0 j
  have hz : (0 : BitVec 32).getLsbD j = false := by
    change (BitVec.ofNat 32 0).getLsbD j = false
    exact BitVec.getLsbD_zero
  have hinit := congrArg (fun b : Bool => (List.range 8).foldl
    (fun out i => out ^^ (boxPiece i (sBox i (roundChunk i r k))).getLsbD j) b) hz
  have hchange := congrArg
    (fun f : Bool → Nat → Bool => (List.range 8).foldl f false) hfold
  exact hbits.trans (hinit.trans (hchange.trans (select_xor _ (boxSource_shape j hj).2.2 _)))

theorem foldl_xor_start (xs : List Nat) (f : Nat → BitVec 64) (a : BitVec 64) :
    xs.foldl (fun out i => out ^^^ f i) a =
      a ^^^ xs.foldl (fun out i => out ^^^ f i) 0 := by
  induction xs generalizing a with
  | nil => simp
  | cons i xs ih =>
    simp only [List.foldl_cons]
    have hz : (0 : BitVec 64) ^^^ f i = f i := BitVec.zero_xor
    rw [hz, ih (a ^^^ f i), ih (f i)]
    exact BitVec.xor_assoc _ _ _

theorem foldl_xor_extend (xs : List Nat) (f : Nat → BitVec 32) (a : BitVec 32) :
    xs.foldl (fun out i => out ^^^ (f i).setWidth 64) (a.setWidth 64) =
      (xs.foldl (fun out i => out ^^^ f i) a).setWidth 64 := by
  induction xs generalizing a with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.foldl_cons]
    rw [← BitVec.setWidth_xor]
    exact ih _

/-- S-box `i`'s piece of the round on the halves' registers. -/
def contribution (r k : BitVec 64) (i : Nat) : BitVec 64 :=
  (boxPiece i (sBox i (roundChunk i (r.setWidth 32) (k.setWidth 48)))).zeroExtend 64

theorem contributions_roundFunction (r k : BitVec 64) (l : BitVec 64) :
    (List.range 8).foldl (fun out i => out ^^^ contribution r k i) l =
      l ^^^ (roundFunction (r.setWidth 32) (k.setWidth 48)).zeroExtend 64 := by
  rw [foldl_xor_start]
  have hf := foldl_xor_extend (List.range 8)
    (fun i => boxPiece i (sBox i (roundChunk i (r.setWidth 32) (k.setWidth 48)))) 0
  have hz : (0 : BitVec 32).setWidth 64 = 0 := BitVec.setWidth_zero 64 32
  have hinit := congrArg (fun b : BitVec 64 =>
    (List.range 8).foldl (fun out i => out ^^^ contribution r k i) b) hz
  have hg := congrArg (BitVec.setWidth 64)
    (boxPieces_eq_roundFunction (r.setWidth 32) (k.setWidth 48))
  exact congrArg (fun x => l ^^^ x) ((hinit.symm.trans hf).trans hg)

end VG.Proof.TripleDes
