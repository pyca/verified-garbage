module

public import VerifiedGarbage.Proof.Aes.Bitsliced
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.Camellia

/-! ### `Camellia.Bytes`, which this module and modules that import it used -/

section

/-!
# Camellia's functions, byte by byte and bit by bit

`byteOf x i` is byte `i` of the 64-bit `x`, from the most significant
(`t(i + 1)` of RFC 3713 §2.4.1). The F-function's byte `i` is the XOR of
the S-boxes of the bytes in row `i` of the P-function (`byteOf_f`); `FL`
and `FLINV` are stated bit by bit (`getLsbD_fl`, `getLsbD_flinv`).
-/

@[expose] public section

namespace VG.Proof.Camellia

open VG VG.Spec.Camellia

/-- Byte `i` of `x`, from the most significant. -/
def byteOf (x : BitVec 64) (i : Nat) : Byte := (x >>> (56 - 8 * i)).setWidth 8

theorem getLsbD_byteOf (x : BitVec 64) {i j : Nat} (_hi : i < 8) (hj : j < 8) :
    (byteOf x i).getLsbD j = x.getLsbD (56 - 8 * i + j) := by
  simp only [byteOf, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hj, decide_true,
    Bool.true_and]

theorem byteOf_xor (x y : BitVec 64) (i : Nat) : byteOf (x ^^^ y) i = byteOf x i ^^^ byteOf y i := by
  simp only [byteOf, BitVec.ushiftRight_xor_distrib, BitVec.setWidth_xor]

/-- The S-box of byte `i` (from 0): `SBOX1, SBOX2, SBOX3, SBOX4, SBOX2, SBOX3,
SBOX4, SBOX1`. -/
def sboxAt : Nat → Byte → Byte
  | 0 => sbox1 | 1 => sbox2 | 2 => sbox3 | 3 => sbox4
  | 4 => sbox2 | 5 => sbox3 | 6 => sbox4 | _ => sbox1

/-- The bytes (from 0) whose S-boxes byte `i` of the P-function's output XORs. -/
def pRow : Nat → List Nat
  | 0 => [0, 2, 3, 5, 6, 7] | 1 => [0, 1, 3, 4, 6, 7] | 2 => [0, 1, 2, 4, 5, 7]
  | 3 => [1, 2, 3, 4, 5, 6] | 4 => [0, 1, 5, 6, 7] | 5 => [1, 2, 4, 6, 7]
  | 6 => [2, 3, 4, 5, 7] | _ => [0, 3, 4, 5, 6]

/-- The XOR of the bits `j` of `t i` for `i ∈ l`. -/
def xorRow (t : Nat → Byte) (l : List Nat) (j : Nat) : Bool :=
  l.foldr (fun i acc => (t i).getLsbD j ^^ acc) false

set_option linter.unusedSimpArgs false in
/-- Bit `56 - 8 i + j` of eight bytes appended is bit `j` of the `i`-th. -/
theorem getLsbD_cat8 (y0 y1 y2 y3 y4 y5 y6 y7 : Byte) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    (y0 ++ y1 ++ y2 ++ y3 ++ y4 ++ y5 ++ y6 ++ y7).getLsbD (56 - 8 * i + j) =
      ([y0, y1, y2, y3, y4, y5, y6, y7].getD i 0).getLsbD j := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega_using [hi]) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [BitVec.getLsbD_append, List.getD_cons_succ, List.getD_cons_zero] <;>
  simp (disch := omega) only [ite_eq_right_of_eq_false, ite_eq_left_of_eq_true, eq_false, eq_true,
    Nat.reduceMul, Nat.reduceSub, ite_true, ite_false] <;>
  congr 1 <;> omega_using []

theorem getLsbD_byteOf_f (x k : BitVec 64) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    (byteOf (f x k) i).getLsbD j =
      xorRow (fun i' => sboxAt i' (byteOf (x ^^^ k) i')) (pRow i) j := by
  have ht : ∀ n, 1 ≤ n → n ≤ 8 →
      ((x ^^^ k) >>> (64 - 8 * n)).setWidth 8 = byteOf (x ^^^ k) (n - 1) := fun n h1 h2 => by
    simp only [byteOf]; congr 2; omega_using [h1]
  -- In one pass: each `rw` would rebuild the whole (large) goal.
  simp only [f, ht 1 (by omega_using []) (by omega_using []), ht 2 (by omega_using []) (by omega_using []), ht 3 (by omega_using []) (by omega_using []),
    ht 4 (by omega_using []) (by omega_using []), ht 5 (by omega_using []) (by omega_using []), ht 6 (by omega_using []) (by omega_using []),
    ht 7 (by omega_using []) (by omega_using []), ht 8 (by omega_using []) (by omega_using [])]
  rw [getLsbD_byteOf _ hi hj, getLsbD_cat8 _ _ _ _ _ _ _ _ hi hj]
  generalize byteOf (x ^^^ k) = b
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega_using [hi]) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [List.getD_cons_succ, List.getD_cons_zero, BitVec.getLsbD_xor, xorRow, pRow, sboxAt,
    List.foldr_cons, List.foldr_nil, Bool.xor_false, Bool.xor_assoc]

/-! ## FL and FLINV, bit by bit

Bit `n` of a 64-bit value; bits `32 … 63` are `x1` (`y1`), `0 … 31` are
`x2` (`y2`), and bit `n` of `x <<< 1` is bit `n - 1` cyclically. -/

theorem getLsbD_fl_lo (x k : BitVec 64) {n : Nat} (hn : n < 32) :
    (fl x k).getLsbD n = (x.getLsbD n ^^ (x.getLsbD (32 + (n + 31) % 32) && k.getLsbD (32 + (n + 31) % 32))) := by
  have hm : (n + 31) % 32 < 32 := Nat.mod_lt _ (by omega_using [])
  simp only [fl, BitVec.getLsbD_append, hn, ite_true, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_rotateLeft, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, decide_true, Bool.true_and]
  split
  · rw [show 32 - 1 % 32 + n = (n + 31) % 32 by omega_arith]; simp [hm]
  · rw [show n - 1 % 32 = (n + 31) % 32 by omega_arith]; simp [hm]

theorem getLsbD_fl_hi (x k : BitVec 64) {n : Nat} (hn : 32 ≤ n) (hn' : n < 64) :
    (fl x k).getLsbD n = (x.getLsbD n ^^ ((fl x k).getLsbD (n - 32) || k.getLsbD (n - 32))) := by
  have h1 : ¬ n < 32 := by omega_using [hn]
  have h2 : n - 32 < 32 := by omega_using [hn']
  simp only [fl, BitVec.getLsbD_append, h1, h2, ite_true, ite_false, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, decide_true, Bool.true_and]
  rw [show 32 + (n - 32) = n by omega_using [hn]]

theorem getLsbD_flinv_hi (x k : BitVec 64) {n : Nat} (hn : 32 ≤ n) (hn' : n < 64) :
    (flinv x k).getLsbD n = (x.getLsbD n ^^ (x.getLsbD (n - 32) || k.getLsbD (n - 32))) := by
  have h1 : ¬ n < 32 := by omega_using [hn]
  have h2 : n - 32 < 32 := by omega_using [hn']
  simp only [flinv, BitVec.getLsbD_append, h1, h2, ite_false, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, decide_true, Bool.true_and]
  rw [show 32 + (n - 32) = n by omega_using [hn]]

theorem getLsbD_flinv_lo (x k : BitVec 64) {n : Nat} (hn : n < 32) :
    (flinv x k).getLsbD n = (x.getLsbD n ^^
      ((flinv x k).getLsbD (32 + (n + 31) % 32) && k.getLsbD (32 + (n + 31) % 32))) := by
  have hm : (n + 31) % 32 < 32 := Nat.mod_lt _ (by omega_using [])
  have h1 : ¬ 32 + (n + 31) % 32 < 32 := by omega_using []
  have h2 : 32 + (n + 31) % 32 - 32 < 32 := by omega_using []
  simp only [flinv, BitVec.getLsbD_append, hn, h1, h2, ite_true, ite_false, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_rotateLeft, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, decide_true, Bool.true_and]
  split
  · rw [show 32 - 1 % 32 + n = (n + 31) % 32 by omega_arith]; simp [hm]
  · rw [show n - 1 % 32 = (n + 31) % 32 by omega_arith]; simp [hm]

end VG.Proof.Camellia

end

end

/-!
# Bitsliced Camellia: the layout and the layers

Eight blocks at a time. A 64-bit half of each block (`D1` or `D2`) is
held in eight 64-bit *planes*: bit `8c + b` of plane `j` is bit `j` of the
half's byte `pos c` (from the most significant) in block `b`. The bytes are
interleaved, `pos = 0 4 1 5 2 6 3 7`, so that the left 32 bits are in the
even bytes of a plane and the right 32 in the odd ones (`HalfRel`).

The lemmas here turn what each layer of the code does to the bits (as its
proof states it, by evaluation or symbolic execution) into the function of
RFC 3713 it computes on the halves: a round (`round_rel`), FL and FLINV
(`fl_rel`, `flinv_rel`). Nothing here depends on the target; the maps from
output bits to input bits (`toBsG`, `keyInG`, `outPG`, …) are what each
target's checks compare its code with.
-/

@[expose] public section

namespace VG.Proof.Camellia

open VG VG.Spec.Camellia VG.Bitslice
open VG.Proof.Aes (bsByte getLsbD_bsByte byte_ext)

/-! ## The layout -/

/-- Byte `c` of a plane holds the half's byte `pos c`. -/
def pos (c : Nat) : Nat := c / 2 + 4 * (c % 2)

/-- The byte of a plane holding the half's byte `i`: the inverse of `pos`. -/
def cpos (i : Nat) : Nat := 2 * (i % 4) + i / 4

theorem pos_lt {c : Nat} (hc : c < 8) : pos c < 8 := by simp only [pos]; omega_arith
theorem cpos_lt {i : Nat} (hi : i < 8) : cpos i < 8 := by simp only [cpos]; omega_arith
theorem pos_cpos {i : Nat} (hi : i < 8) : pos (cpos i) = i := by simp only [pos, cpos]; omega_arith
/-- The planes `Q` hold the halves `d b` of the eight blocks. -/
def HalfRel (Q : Nat → BitVec 64) (d : Nat → BitVec 64) : Prop :=
  ∀ b < 8, ∀ c < 8, ∀ j < 8, (Q j).getLsbD (8 * c + b) = (byteOf (d b) (pos c)).getLsbD j

theorem HalfRel.congr {Q Q' : Nat → BitVec 64} {d : Nat → BitVec 64} (h : HalfRel Q d)
    (he : ∀ j < 8, Q' j = Q j) : HalfRel Q' d := fun b hb c hc j hj => by
  rw [he j hj]; exact h b hb c hc j hj

/-! ## The maps of the linear layers

Output bit `p` of output word `j` is the XOR of the input bits `g j p`, bit
`t` of input word `i` being `64 i + t`: the state's planes are input words
`0 … 7`, and the subkey's planes at the table entry words `8 …`. -/

/-- Bitslicing: bit `8c + b` of plane `j` is bit `j` of byte `pos c` of
(little-endian) word `b`. -/
def toBsG (j p : Nat) : List Nat := [64 * (p % 8) + 8 * pos (p / 8) + j]

/-- Back: bit `t` of word `b` is bit `t % 8` of byte `cpos (t / 8)` of block `b`. -/
def fromBsG (b t : Nat) : List Nat := [64 * (t % 8) + 8 * cpos (t / 8) + b]

/-- The plane that input selection takes for plane `j` in byte `c`: `SBOX4`'s
bytes (5 and 6, holding `t7` and `t4`) rotate their input left by a bit. -/
def inSrc (c j : Nat) : Nat := if c = 5 ∨ c = 6 then (j + 7) % 8 else j

/-- The subkey XOR and input selection, with the subkey's planes at words
`8 + off … 15 + off`. -/
def keyInG (off j p : Nat) : List Nat :=
  [64 * inSrc (p / 8) j + p, 64 * (8 + off + inSrc (p / 8) j) + p]

/-- The plane that output selection takes for plane `j` in byte `c`:
`SBOX2`'s bytes (1 and 2) rotate their output left by a bit, `SBOX3`'s (3
and 4) right. -/
def outSrc (c j : Nat) : Nat :=
  if c = 1 ∨ c = 2 then (j + 7) % 8 else if c = 3 ∨ c = 4 then (j + 1) % 8 else j

/-- The output selection and the P-function: bit `8c + b` of plane `j` is
the XOR, over the bytes `i` of row `pos c` of the P-function, of the
selected plane's bit in byte `cpos i`. -/
def outPG (j p : Nat) : List Nat :=
  (pRow (pos (p / 8))).map fun i => 64 * outSrc (cpos i) j + 8 * cpos i + p % 8

/-! ## A round -/

theorem rotl1_bit (x : Byte) {j : Nat} (hj : j < 8) :
    (x.rotateLeft 1).getLsbD j = x.getLsbD ((j + 7) % 8) := by
  rw [BitVec.getLsbD_rotateLeft]
  split
  · congr 1; omega_arith
  · rw [show j - 1 % 8 = (j + 7) % 8 by omega_arith]; simp [hj]

theorem rotl7_bit (x : Byte) {j : Nat} (hj : j < 8) :
    (x.rotateLeft 7).getLsbD j = x.getLsbD ((j + 1) % 8) := by
  rw [BitVec.getLsbD_rotateLeft]
  split
  · congr 1; omega_arith
  · rw [show j - 7 % 8 = (j + 1) % 8 by omega_arith]; simp [hj]

/-- The S-box bytes: input bit `inSrc` and output bit `outSrc` of `SBOX1`
make the S-box of the byte's position. -/
theorem sbox_sel {x : Byte} {c j : Nat} (hc : c < 8) (hj : j < 8) :
    (sbox1 (ofBits 8 fun j' => x.getLsbD (inSrc c j'))).getLsbD (outSrc c j) =
      (sboxAt (pos c) x).getLsbD j := by
  have hin : (ofBits 8 fun j' => x.getLsbD (inSrc c j')) =
      if c = 5 ∨ c = 6 then x.rotateLeft 1 else x := by
    refine byte_ext fun j' hj' => ?_
    rw [getLsbD_ofBits]
    simp only [inSrc, hj', decide_true, Bool.true_and]
    split
    · rw [rotl1_bit _ hj']
    · rfl
  rw [hin]
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 by omega_arith) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [outSrc, pos, sboxAt, sbox2, sbox3, sbox4, rotl1_bit _ hj, rotl7_bit _ hj]

/-- The XOR of the bits of the selected planes `S` along a row. -/
def rowBits (S : Nat → BitVec 64) (j b : Nat) (l : List Nat) : Bool :=
  l.foldr (fun i acc => (S (outSrc (cpos i) j)).getLsbD (8 * cpos i + b) ^^ acc) false

theorem rowBits_eq {S : Nat → BitVec 64} {t : Nat → Byte} {j b : Nat} {l : List Nat}
    (hl : ∀ i ∈ l, (S (outSrc (cpos i) j)).getLsbD (8 * cpos i + b) = (t i).getLsbD j) :
    rowBits S j b l = xorRow t l j := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [rowBits, xorRow, List.foldr_cons] at ih ⊢
    rw [hl i List.mem_cons_self, ih fun i' hi' => hl i' (List.mem_cons_of_mem _ hi')]

theorem pRow_lt {i c : Nat} (h : i ∈ pRow c) : i < 8 := by
  unfold pRow at h; split at h <;> simp at h <;> omega_arith

/-- A round: from the half `d1` and the subkey `k` in the planes `Q` and `K`,
the code computes `X` (the subkey XOR and input selection), `S` (`SBOX1`),
`Y` (output selection and the P-function) and XORs it into the other half
`d2`, in `R`: `R'` holds `d2 ^ F(d1, k)`. -/
theorem round_rel {Q K R X S Y R' : Nat → BitVec 64} {d1 d2 : Nat → BitVec 64} {k : BitVec 64}
    (hQ : HalfRel Q d1) (hK : HalfRel K fun _ => k) (hR : HalfRel R d2)
    (hX : ∀ j < 8, ∀ p < 64,
      (X j).getLsbD p = ((Q (inSrc (p / 8) j)).getLsbD p ^^ (K (inSrc (p / 8) j)).getLsbD p))
    (hS : ∀ j < 8, ∀ p < 64, (S j).getLsbD p = (sbox1 (bsByte X p)).getLsbD j)
    (hY : ∀ j < 8, ∀ p < 64, (Y j).getLsbD p = rowBits S j (p % 8) (pRow (pos (p / 8))))
    (hR' : ∀ j < 8, ∀ p < 64, (R' j).getLsbD p = ((R j).getLsbD p ^^ (Y j).getLsbD p)) :
    HalfRel R' fun b => d2 b ^^^ f (d1 b) k := by
  intro b hb c hc j hj
  have hp : 8 * c + b < 64 := by omega_arith
  rw [hR' j hj _ hp, hR b hb c hc j hj, byteOf_xor, BitVec.getLsbD_xor,
    getLsbD_byteOf_f _ _ (pos_lt hc) hj, hY j hj _ hp]
  congr 1
  rw [show (8 * c + b) % 8 = b by omega_arith, show (8 * c + b) / 8 = c by omega_arith]
  refine rowBits_eq fun i hi => ?_
  have hi8 := pRow_lt hi
  have hc' := cpos_lt hi8
  rw [hS _ (by simp only [outSrc]; split <;> (try split) <;> omega_arith) _ (by omega_arith)]
  have hx : bsByte X (8 * cpos i + b) =
      ofBits 8 fun j' => (byteOf (d1 b ^^^ k) i).getLsbD (inSrc (cpos i) j') := by
    refine byte_ext fun j' hj' => ?_
    have hs : inSrc (cpos i) j' < 8 := by simp only [inSrc]; split <;> omega_arith
    rw [getLsbD_bsByte _ _ hj', getLsbD_ofBits]
    simp only [hj', decide_true, Bool.true_and]
    rw [hX j' hj' _ (by omega_arith), show (8 * cpos i + b) / 8 = cpos i by omega_arith,
      hQ b hb _ hc' _ hs, hK b hb _ hc' _ hs, pos_cpos hi8, byteOf_xor, BitVec.getLsbD_xor]
  rw [hx, sbox_sel hc' hj, pos_cpos hi8]

/-! ## FL and FLINV

`x2 ^= (x1 & k1) <<< 1` (`RotStep`): in the odd bytes, plane `j` takes the
AND of plane `j - 1` and the subkey's in the even byte below (for `j ≥ 1`),
or of plane 7 in the even byte above, cyclically (for `j = 0`, the bit that
the rotation moves to the next byte). `x1 ^= x2 | k2` (`OrStep`): in the
even bytes, plane `j` takes the OR of its own and the subkey's in the odd
byte above. -/

/-- Whether bit position `p` is in an odd byte (the right half). -/
def oddAt (p : Nat) : Bool := (p / 8) % 2 == 1

/-- The position the rotation step reads for position `p` of plane `j`. -/
def rotPos (j p : Nat) : Nat := (p + if j = 0 then 8 else 56) % 64

def RotStep (Q K Q' : Nat → BitVec 64) : Prop :=
  ∀ j < 8, ∀ p < 64, (Q' j).getLsbD p = ((Q j).getLsbD p ^^
    (oddAt p && (Q ((j + 7) % 8)).getLsbD (rotPos j p) && (K ((j + 7) % 8)).getLsbD (rotPos j p)))

def OrStep (Q K Q' : Nat → BitVec 64) : Prop :=
  ∀ j < 8, ∀ p < 64, (Q' j).getLsbD p = ((Q j).getLsbD p ^^
    (!oddAt p && ((Q j).getLsbD ((p + 8) % 64) || (K j).getLsbD ((p + 8) % 64))))

/-- Bit `j` of byte `i` of `x` is bit `56 - 8 i + j` (`getLsbD_byteOf`), stated
for the halves' planes. -/
theorem oddAt_even {m b : Nat} (hb : b < 8) : oddAt (8 * (2 * m) + b) = false := by
  unfold oddAt; rw [show (8 * (2 * m) + b) / 8 % 2 = 0 by omega_arith]; rfl

theorem oddAt_odd {m b : Nat} (hb : b < 8) : oddAt (8 * (2 * m + 1) + b) = true := by
  unfold oddAt; rw [show (8 * (2 * m + 1) + b) / 8 % 2 = 1 by omega_arith]; rfl

theorem pos_even {m : Nat} (_hm : m < 4) : pos (2 * m) = m := by simp only [pos]; omega_arith
theorem pos_odd {m : Nat} (_hm : m < 4) : pos (2 * m + 1) = 4 + m := by simp only [pos]; omega_arith

theorem half_bit {Q : Nat → BitVec 64} {d : Nat → BitVec 64} (h : HalfRel Q d) {b c j : Nat}
    (hb : b < 8) (hc : c < 8) (hj : j < 8) :
    (Q j).getLsbD (8 * c + b) = (d b).getLsbD (56 - 8 * pos c + j) := by
  rw [h b hb c hc j hj, getLsbD_byteOf _ (pos_lt hc) hj]

/-- The rotation step, in the odd bytes, is `x2 ^ (x1 & k1) <<< 1`: bit `n < 32`. -/
theorem rot_bit {Q K Q' : Nat → BitVec 64} {d : Nat → BitVec 64} {k : BitVec 64}
    (hQ : HalfRel Q d) (hK : HalfRel K fun _ => k) (hr : RotStep Q K Q') {b m j : Nat}
    (hb : b < 8) (hm : m < 4) (hj : j < 8) :
    (Q' j).getLsbD (8 * (2 * m + 1) + b) = ((d b).getLsbD (24 - 8 * m + j) ^^
      ((d b).getLsbD (32 + (24 - 8 * m + j + 31) % 32) && k.getLsbD (32 + (24 - 8 * m + j + 31) % 32))) := by
  have hp : 8 * (2 * m + 1) + b < 64 := by omega_arith
  rw [hr j hj _ hp, half_bit hQ hb (by omega_arith) hj]
  have hodd : oddAt (8 * (2 * m + 1) + b) = true := oddAt_odd hb
  have hpos : pos (2 * m + 1) = 4 + m := pos_odd hm
  simp only [hodd, Bool.true_and, hpos, show 56 - 8 * (4 + m) + j = 24 - 8 * m + j by omega_arith]
  congr 1
  have hj7 : (j + 7) % 8 < 8 := Nat.mod_lt _ (by omega_arith)
  by_cases hj0 : j = 0
  · subst hj0
    have hrp : rotPos 0 (8 * (2 * m + 1) + b) = 8 * ((2 * m + 2) % 8) + b := by
      simp only [rotPos, ↓reduceIte]; omega_arith
    rw [hrp, half_bit hQ hb (by omega_arith) hj7, half_bit hK hb (by omega_arith) hj7]
    have : 56 - 8 * pos ((2 * m + 2) % 8) + (0 + 7) % 8 = 32 + (24 - 8 * m + 0 + 31) % 32 := by
      simp only [pos]; omega_arith
    rw [this]
  · have hrp : rotPos j (8 * (2 * m + 1) + b) = 8 * (2 * m) + b := by
      simp only [rotPos, hj0, ↓reduceIte]; omega_arith
    rw [hrp, half_bit hQ hb (by omega_arith) hj7, half_bit hK hb (by omega_arith) hj7]
    have : 56 - 8 * pos (2 * m) + (j + 7) % 8 = 32 + (24 - 8 * m + j + 31) % 32 := by
      simp only [pos]; omega_arith
    rw [this]

theorem fl_rel {Q K Q₁ Q₂ : Nat → BitVec 64} {d : Nat → BitVec 64} {k : BitVec 64}
    (hQ : HalfRel Q d) (hK : HalfRel K fun _ => k) (h₁ : RotStep Q K Q₁) (h₂ : OrStep Q₁ K Q₂) :
    HalfRel Q₂ fun b => fl (d b) k := by
  -- The odd bytes, after the first step.
  have hodd : ∀ b < 8, ∀ m < 4, ∀ j < 8,
      (Q₁ j).getLsbD (8 * (2 * m + 1) + b) = (fl (d b) k).getLsbD (24 - 8 * m + j) := by
    intro b hb m hm j hj
    rw [rot_bit hQ hK h₁ hb hm hj, getLsbD_fl_lo _ _ (by omega_arith)]
  intro b hb c hc j hj
  dsimp only
  have hp : 8 * c + b < 64 := by omega_arith
  rw [getLsbD_byteOf _ (pos_lt hc) hj, h₂ j hj _ hp]
  obtain ⟨m, rfl | rfl⟩ : ∃ m, c = 2 * m ∨ c = 2 * m + 1 := ⟨c / 2, by omega_arith⟩
  · -- The left half: `x1 ^ (x2 | k2)`.
    have hm : m < 4 := by omega_arith
    have hp8 : (8 * (2 * m) + b + 8) % 64 = 8 * (2 * m + 1) + b := by omega_arith
    have h1 : (Q₁ j).getLsbD (8 * (2 * m) + b) = (d b).getLsbD (56 - 8 * m + j) := by
      rw [h₁ j hj _ (by omega_arith), oddAt_even hb, Bool.false_and, Bool.false_and, Bool.xor_false,
        half_bit hQ hb (by omega_arith) hj, pos_even hm]
    have h2 : (K j).getLsbD (8 * (2 * m + 1) + b) = k.getLsbD (24 - 8 * m + j) := by
      rw [half_bit hK hb (by omega_arith) hj, pos_odd hm, show 56 - 8 * (4 + m) + j = 24 - 8 * m + j by omega_arith]
    rw [oddAt_even hb, pos_even hm, hp8, hodd b hb m hm j hj, h1, h2, Bool.not_false, Bool.true_and,
      getLsbD_fl_hi (d b) k (n := 56 - 8 * m + j) (by omega_arith) (by omega_arith),
      show 56 - 8 * m + j - 32 = 24 - 8 * m + j by omega_arith]
  · -- The right half.
    have hm : m < 4 := by omega_arith
    rw [oddAt_odd hb, pos_odd hm, hodd b hb m hm j hj, Bool.not_true, Bool.false_and, Bool.xor_false,
      show 56 - 8 * (4 + m) + j = 24 - 8 * m + j by omega_arith]

theorem flinv_rel {Q K Q₁ Q₂ : Nat → BitVec 64} {d : Nat → BitVec 64} {k : BitVec 64}
    (hQ : HalfRel Q d) (hK : HalfRel K fun _ => k) (h₁ : OrStep Q K Q₁) (h₂ : RotStep Q₁ K Q₂) :
    HalfRel Q₂ fun b => flinv (d b) k := by
  -- After the first step, the left half is `y1 ^ (y2 | k2)`, the right `y2`.
  let Y : Nat → BitVec 64 := fun b => ((flinv (d b) k) >>> 32).setWidth 32 ++ (d b).setWidth 32
  have hYhi : ∀ b, ∀ n, 32 ≤ n → n < 64 → (Y b).getLsbD n = (flinv (d b) k).getLsbD n := by
    intro b n h1 h2
    simp only [Y, BitVec.getLsbD_append, show ¬ n < 32 by omega_arith, ite_false,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, show n - 32 < 32 by omega_arith, decide_true,
      Bool.true_and]
    congr 1; omega_arith
  have hYlo : ∀ b, ∀ n, n < 32 → (Y b).getLsbD n = (d b).getLsbD n := by
    intro b n h1
    simp only [Y, BitVec.getLsbD_append, h1, ite_true, BitVec.getLsbD_setWidth, decide_true,
      Bool.true_and]
  have h₁r : HalfRel Q₁ Y := by
    intro b hb c hc j hj
    have hp : 8 * c + b < 64 := by omega_arith
    rw [getLsbD_byteOf _ (pos_lt hc) hj, h₁ j hj _ hp]
    obtain ⟨m, rfl | rfl⟩ : ∃ m, c = 2 * m ∨ c = 2 * m + 1 := ⟨c / 2, by omega_arith⟩
    · have hm : m < 4 := by omega_arith
      rw [oddAt_even hb, pos_even hm, show (8 * (2 * m) + b + 8) % 64 = 8 * (2 * m + 1) + b by omega_arith,
        half_bit hQ hb (by omega_arith) hj, half_bit hQ hb (by omega_arith) hj, half_bit hK hb (by omega_arith) hj,
        pos_even hm, pos_odd hm, hYhi b _ (by omega_arith) (by omega_arith),
        getLsbD_flinv_hi (d b) k (n := 56 - 8 * m + j) (by omega_arith) (by omega_arith),
        show 56 - 8 * (4 + m) + j = 56 - 8 * m + j - 32 by omega_arith]
      simp only [Bool.not_false, Bool.true_and]
    · have hm : m < 4 := by omega_arith
      rw [oddAt_odd hb, pos_odd hm, Bool.not_true, Bool.false_and, Bool.xor_false,
        half_bit hQ hb (by omega_arith) hj, pos_odd hm, hYlo b _ (by omega_arith)]
  intro b hb c hc j hj
  dsimp only
  rw [getLsbD_byteOf _ (pos_lt hc) hj]
  obtain ⟨m, rfl | rfl⟩ : ∃ m, c = 2 * m ∨ c = 2 * m + 1 := ⟨c / 2, by omega_arith⟩
  · have hm : m < 4 := by omega_arith
    rw [h₂ j hj _ (by omega_arith), oddAt_even hb, Bool.false_and, Bool.false_and, Bool.xor_false,
      half_bit h₁r hb (by omega_arith) hj, pos_even hm, hYhi b _ (by omega_arith) (by omega_arith)]
  · have hm : m < 4 := by omega_arith
    rw [rot_bit h₁r hK h₂ hb hm hj, pos_odd hm, hYlo b _ (by omega_arith), hYhi b _ (by omega_arith) (by omega_arith),
      show 56 - 8 * (4 + m) + j = 24 - 8 * m + j by omega_arith,
      getLsbD_flinv_lo (d b) k (n := 24 - 8 * m + j) (by omega_arith)]

end VG.Proof.Camellia
