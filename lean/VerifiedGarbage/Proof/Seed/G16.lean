import VerifiedGarbage.Proof.Seed.G
import VerifiedGarbage.Proof.Aes.Bitsliced
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms

/-!
# G on sixteen words, bitsliced

The words: sixteen 32-bit words in eight 64-bit words `In` (word `w` in half
`w % 2` of `In (w / 2)`, `wordQ`), so 64 bytes, byte `n` in byte `n % 8` of
`In (n / 8)` (`byteQ`). Each target's code for sixteen `G`s at once
(`Impl/Seed/<Target>/G16.lean`) transposes them, so that bit `j` of byte `n`
is at position `laneOf n` of plane `j`, and computes in three steps, which
its proof states as below:

1. `Pl`, the planes of `M` of each byte: bit `p` of plane `j` is the XOR of
   the input bits `l1 j p` (a linear layer, checked by evaluation);
2. `S`, the AES S-box of each byte of `Pl` (`hS`, from AES's proof);
3. `Out`: bit `t` of output word `i` is bit `t` of `gConst` XOR the bits
   `l2 i t` of `S` (a linear layer).

`g16_words` then gives `G` of every input word.
-/

namespace VG.Proof.Seed

open VG VG.Bitslice VG.Impl.Seed VG.Proof.Aes

/-- Byte `n`'s position in the planes (and back: `laneOf_laneOf`). -/
def laneOf (n : Nat) : Nat := 8 * (n % 8) + n / 8

theorem laneOf_lt {n : Nat} (hn : n < 64) : laneOf n < 64 := by unfold laneOf; omega_arith

theorem laneOf_laneOf {n : Nat} (hn : n < 64) : laneOf (laneOf n) = n := by unfold laneOf; omega_arith

/-- Byte `n` of the eight words. -/
def byteQ (In : Nat → BitVec 64) (n : Nat) : Byte := ((In (n / 8)) >>> (8 * (n % 8))).setWidth 8

/-- Word `w` of the eight words. -/
def wordQ (Q : Nat → BitVec 64) (w : Nat) : Spec.Seed.Word := ((Q (w / 2)) >>> (32 * (w % 2))).setWidth 32

/-- The input bits of bit `p` of plane `j` of `M`: bits `M`'s row `j` of the
byte at `p`. -/
def l1 (j p : Nat) : List Nat := (mRows.getD j []).map fun b => 8 * laneOf p + b

/-- The bits of the S-box outputs that bit `t` of output word `i` XORs:
those of each byte `a` of its 32-bit word that `G` keeps (`maskOf`), of
`P0` or `P1`. -/
def l2 (i t : Nat) : List Nat :=
  (List.range 4).flatMap fun a =>
    if (maskOf ((a + t % 32 / 8) % 4)).getLsbD (t % 8) then
      ((pRows (a % 2 == 1)).getD (t % 8) []).map fun j => 64 * j + laneOf (8 * i + 4 * (t / 32) + a)
    else []

/-! ## Lemmas -/

theorem xorBits_append (W : Nat → BitVec 64) (l l' : List Nat) :
    xorBits W (l ++ l') = (xorBits W l ^^ xorBits W l') := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem xorBits_ite (W : Nat → BitVec 64) (c : Bool) (l : List Nat) :
    xorBits W (if c then l else []) = (c && xorBits W l) := by
  cases c <;> simp

theorem xorBits_range4 (W : Nat → BitVec 64) (f : Nat → List Nat) :
    xorBits W ((List.range 4).flatMap f) = xor4 fun a => xorBits W (f a) := by
  simp [List.range_succ, xorBits_append, xor4]

/-- Bits `l` (each below 8) of byte `n`. -/
theorem xorBits_byte (In : Nat → BitVec 64) {n : Nat} {l : List Nat} (hl : ∀ b ∈ l, b < 8) :
    xorBits In (l.map fun b => 8 * n + b) = xorOf (byteQ In n) l := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have hb := hl b List.mem_cons_self
    simp only [List.map_cons, xorBits_cons, xorOf_cons, ih fun b h => hl b (List.mem_cons_of_mem _ h)]
    congr 1
    simp only [bitOf, byteQ, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hb, decide_true,
      Bool.true_and]
    rw [show (8 * n + b) / 64 = n / 8 by omega_arith, show (8 * n + b) % 64 = 8 * (n % 8) + b by omega_arith]

/-- Bits `l` (each below 8) of the planes `S` at `p`. -/
theorem xorBits_planes (S : Nat → BitVec 64) {p : Nat} (hp : p < 64) {l : List Nat}
    (hl : ∀ j ∈ l, j < 8) : xorBits S (l.map fun j => 64 * j + p) = xorOf (bsByte S p) l := by
  induction l with
  | nil => simp
  | cons j l ih =>
    have hj := hl j List.mem_cons_self
    simp only [List.map_cons, xorBits_cons, xorOf_cons, ih fun b h => hl b (List.mem_cons_of_mem _ h),
      getLsbD_bsByte _ _ hj]
    congr 1
    simp only [bitOf]
    rw [show (64 * j + p) / 64 = j by omega_arith, show (64 * j + p) % 64 = p by omega_arith]

theorem rows_getD_lt {rows : List (List Nat)} (hr : ∀ l ∈ rows, ∀ i ∈ l, i < 8) (j : Nat) :
    ∀ i ∈ rows.getD j [], i < 8 := by
  intro i h
  by_cases hj : j < rows.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at h
    exact hr _ (List.getElem_mem hj) i h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega_arith), Option.getD_none] at h
    cases h

theorem pRows_lt (odd : Bool) : ∀ l ∈ pRows odd, ∀ i ∈ l, i < 8 := by
  cases odd
  · exact rows_lt p0Rows (by simp)
  · exact rows_lt p1Rows (by simp)

theorem byteQ_eq_byteOf (In : Nat → BitVec 64) {w a : Nat} (ha : a < 4) :
    byteQ In (8 * (w / 2) + 4 * (w % 2) + a) = byteOf (wordQ In w) a := by
  refine byte_ext fun b hb => ?_
  rw [getLsbD_byteOf _ hb]
  simp only [byteQ, wordQ, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hb, decide_true,
    Bool.true_and, show 8 * a + b < 32 by omega_arith, decide_true]
  rw [show (8 * (w / 2) + 4 * (w % 2) + a) / 8 = w / 2 by omega_arith,
    show 8 * ((8 * (w / 2) + 4 * (w % 2) + a) % 8) + b = 32 * (w % 2) + (8 * a + b) by omega_arith]

/-- `gConst`'s bits: the S-boxes' constants, mixed as `G` mixes. -/
theorem gConst_bits : ∀ h < 2, ∀ a' < 4, ∀ tb < 8, gConst.getLsbD (32 * h + 8 * a' + tb) =
    xor4 fun a => (sConst (a % 2 == 1)).getLsbD tb && (maskOf ((a + a') % 4)).getLsbD tb := by
  decide

theorem xor4_split (L c m : Nat → Bool) :
    (xor4 fun a => (L a ^^ c a) && m a) = ((xor4 fun a => m a && L a) ^^ xor4 fun a => c a && m a) := by
  simp only [xor4, Bool.and_xor_distrib_right, Bool.and_comm (m _)]
  simp only [Bool.xor_assoc, Bool.xor_left_comm]

/-! ## The theorem -/

theorem g16_words {In Pl S Out : Nat → BitVec 64}
    (h1 : ∀ j < 8, ∀ p < 64, (Pl j).getLsbD p = xorBits In (l1 j p))
    (hS : ∀ j < 8, ∀ p < 64, (S j).getLsbD p = (Spec.Aes.sbox (bsByte Pl p)).getLsbD j)
    (h2 : ∀ i < 8, ∀ t < 64, (Out i).getLsbD t = (gConst.getLsbD t ^^ xorBits S (l2 i t))) :
    ∀ w < 16, wordQ Out w = Spec.Seed.g (wordQ In w) := by
  -- The planes of `M`, and of the S-box.
  have hPl : ∀ p < 64, bsByte Pl p = linB mRows (byteQ In (laneOf p)) := by
    intro p hp
    refine byte_ext fun j hj => ?_
    rw [getLsbD_bsByte _ _ hj, h1 j hj p hp, getLsbD_linB _ _ hj, l1,
      xorBits_byte _ (rows_getD_lt (rows_lt mRows (by simp)) j)]
  have hSb : ∀ p < 64, bsByte S p = Spec.Aes.sbox (bsByte Pl p) := by
    intro p hp
    exact byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, hS j hj p hp]
  intro w hw
  apply BitVec.eq_of_getLsbD_eq
  intro t' ht'
  have hi : w / 2 < 8 := by omega_arith
  have ht : 32 * (w % 2) + t' < 64 := by omega_arith
  have hwq : (wordQ Out w).getLsbD t' = (Out (w / 2)).getLsbD (32 * (w % 2) + t') := by
    simp only [wordQ, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, ht', decide_true,
      Bool.true_and]
  rw [hwq, h2 _ hi _ ht, show t' = 8 * (t' / 8) + t' % 8 by omega_arith,
    getLsbD_g _ (by omega_arith) (Nat.mod_lt _ (by omega_arith))]
  rw [show 32 * (w % 2) + (8 * (t' / 8) + t' % 8) = 32 * (w % 2) + 8 * (t' / 8) + t' % 8 by omega_arith,
    gConst_bits _ (Nat.mod_lt _ (by omega_arith)) _ (by omega_arith) _ (Nat.mod_lt _ (by omega_arith))]
  -- The S-box outputs of byte `a`.
  have hbyte : ∀ a < 4, xorBits S
      (((pRows (a % 2 == 1)).getD (t' % 8) []).map fun j =>
        64 * j + laneOf (8 * (w / 2) + 4 * (w % 2) + a)) =
      (linB (pRows (a % 2 == 1)) (Spec.Aes.sbox (linB mRows (byteOf (wordQ In w) a)))).getLsbD
        (t' % 8) := by
    intro a ha
    have hn : 8 * (w / 2) + 4 * (w % 2) + a < 64 := by omega_arith
    rw [xorBits_planes _ (laneOf_lt hn) (rows_getD_lt (pRows_lt _) _), hSb _ (laneOf_lt hn),
      hPl _ (laneOf_lt hn), laneOf_laneOf hn, byteQ_eq_byteOf _ ha,
      getLsbD_linB _ _ (Nat.mod_lt _ (by omega_arith))]
  have hl2 : xorBits S (l2 (w / 2) (32 * (w % 2) + 8 * (t' / 8) + t' % 8)) =
      xor4 fun a => (maskOf ((a + t' / 8) % 4)).getLsbD (t' % 8) &&
        (linB (pRows (a % 2 == 1)) (Spec.Aes.sbox (linB mRows (byteOf (wordQ In w) a)))).getLsbD
          (t' % 8) := by
    have e1 : (32 * (w % 2) + 8 * (t' / 8) + t' % 8) % 32 / 8 = t' / 8 := by omega_arith
    have e2 : (32 * (w % 2) + 8 * (t' / 8) + t' % 8) % 8 = t' % 8 := by omega_arith
    have e3 : (32 * (w % 2) + 8 * (t' / 8) + t' % 8) / 32 = w % 2 := by omega_arith
    rw [l2, e1, e2, e3, xorBits_range4]
    simp only [xor4, xorBits_ite]
    rw [hbyte 0 (by omega_arith), hbyte 1 (by omega_arith), hbyte 2 (by omega_arith), hbyte 3 (by omega_arith)]
  rw [hl2]
  simp only [sOf, sbox_eq, BitVec.getLsbD_xor]
  rw [xor4_split, Bool.xor_comm]

end VG.Proof.Seed
