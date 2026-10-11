import VerifiedGarbage.Proof.Seed.G16
import VerifiedGarbage.Proof.Aes.Ct32.Bitsliced
import VerifiedGarbage.Impl.Seed.W32

/-!
# G on eight words, bitsliced in 32-bit planes

As `G16.lean`, for the 32-bit targets: eight 32-bit words `In`, so 32
bytes, byte `n` in byte `n % 4` of `In (n / 4)` (`byteW`). Each target's
code for eight `G`s at once (`Impl/Seed/<Target>/G8.lean`) transposes
them, so that bit `j` of byte `n` is at position `laneOf8 n` of plane `j`,
and computes in three steps, which its proof states as below:

1. `Pl`, the planes of `M` of each byte: bit `p` of plane `j` is the XOR of
   the input bits `l1w j p` (a linear layer, checked by evaluation);
2. `S`, the AES S-box of each byte of `Pl` (`hS`, from AES's proof);
3. `Out`: bit `t` of output word `i` is bit `t` of `gConst32` XOR the bits
   `l2w i t` of `S` (a linear layer).

`g8_words` then gives `G` of every input word. Nothing here depends on the
target.
-/

namespace VG.Proof.Seed

open VG VG.Bitslice VG.Impl.Seed VG.Proof.Aes
open VG.Impl.Seed.W32 (gConst32)
open VG.Proof.Aes.Ct32 (bsByte)

/-- Byte `n`'s position in the planes: byte `a` of word `i` is at `8a + i`. -/
def laneOf8 (n : Nat) : Nat := 8 * (n % 4) + n / 4

/-- The byte at position `p` of the planes (`byteOf8_laneOf8`). -/
def byteOf8 (p : Nat) : Nat := 4 * (p % 8) + p / 8

theorem laneOf8_lt {n : Nat} (hn : n < 32) : laneOf8 n < 32 := by unfold laneOf8; omega

theorem byteOf8_laneOf8 {n : Nat} (hn : n < 32) : byteOf8 (laneOf8 n) = n := by
  unfold laneOf8 byteOf8; omega

/-- Byte `n` of the eight words. -/
def byteW (In : Nat → BitVec 32) (n : Nat) : Byte := ((In (n / 4)) >>> (8 * (n % 4))).setWidth 8

/-- The input bits of bit `p` of plane `j` of `M`: bits `M`'s row `j` of the
byte at `p`. -/
def l1w (j p : Nat) : List Nat := (mRows.getD j []).map fun b => 8 * byteOf8 p + b

/-- The bits of the S-box outputs that bit `t` of output word `i` XORs:
those of each byte `a` of the word that `G` keeps (`maskOf`), of `P0` or
`P1`. -/
def l2w (i t : Nat) : List Nat :=
  (List.range 4).flatMap fun a =>
    if (maskOf ((a + t / 8) % 4)).getLsbD (t % 8) then
      ((pRows (a % 2 == 1)).getD (t % 8) []).map fun j => 32 * j + laneOf8 (4 * i + a)
    else []

theorem xorBits_append32 (W : Nat → BitVec 32) (l l' : List Nat) :
    xorBits W (l ++ l') = (xorBits W l ^^ xorBits W l') := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem xorBits_ite32 (W : Nat → BitVec 32) (c : Bool) (l : List Nat) :
    xorBits W (if c then l else []) = (c && xorBits W l) := by
  cases c <;> simp

theorem xorBits_range4_32 (W : Nat → BitVec 32) (f : Nat → List Nat) :
    xorBits W ((List.range 4).flatMap f) = xor4 fun a => xorBits W (f a) := by
  simp [List.range_succ, xorBits_append32, xor4]

/-- Bits `l` (each below 8) of byte `n`. -/
theorem xorBits_byteW (In : Nat → BitVec 32) {n : Nat} {l : List Nat} (hl : ∀ b ∈ l, b < 8) :
    xorBits In (l.map fun b => 8 * n + b) = xorOf (byteW In n) l := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have hb := hl b List.mem_cons_self
    simp only [List.map_cons, xorBits_cons, xorOf_cons, ih fun b h => hl b (List.mem_cons_of_mem _ h)]
    congr 1
    simp only [bitOf, byteW, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hb, decide_true,
      Bool.true_and]
    rw [show (8 * n + b) / 32 = n / 4 by omega, show (8 * n + b) % 32 = 8 * (n % 4) + b by omega]

/-- Bits `l` (each below 8) of the planes `S` at `p`. -/
theorem xorBits_planesW (S : Nat → BitVec 32) {p : Nat} (hp : p < 32) {l : List Nat}
    (hl : ∀ j ∈ l, j < 8) : xorBits S (l.map fun j => 32 * j + p) = xorOf (bsByte S p) l := by
  induction l with
  | nil => simp
  | cons j l ih =>
    have hj := hl j List.mem_cons_self
    simp only [List.map_cons, xorBits_cons, xorOf_cons, ih fun b h => hl b (List.mem_cons_of_mem _ h),
      Ct32.getLsbD_bsByte _ _ hj]
    congr 1
    simp only [bitOf]
    rw [show (32 * j + p) / 32 = j by omega, show (32 * j + p) % 32 = p by omega]

theorem byteW_eq_byteOf (In : Nat → BitVec 32) {w a : Nat} (ha : a < 4) :
    byteW In (4 * w + a) = byteOf (In w) a := by
  refine byte_ext fun b hb => ?_
  rw [getLsbD_byteOf _ hb]
  simp only [byteW, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hb, decide_true,
    Bool.true_and]
  rw [show (4 * w + a) / 4 = w by omega, show 8 * ((4 * w + a) % 4) + b = 8 * a + b by omega]

/-- `gConst32`'s bits: the S-boxes' constants, mixed as `G` mixes. -/
theorem gConst32_bits : ∀ a' < 4, ∀ tb < 8, gConst32.getLsbD (8 * a' + tb) =
    xor4 fun a => (sConst (a % 2 == 1)).getLsbD tb && (maskOf ((a + a') % 4)).getLsbD tb := by
  decide

/-! ## The theorem -/

theorem g8_words {In Pl S Out : Nat → BitVec 32}
    (h1 : ∀ j < 8, ∀ p < 32, (Pl j).getLsbD p = xorBits In (l1w j p))
    (hS : ∀ j < 8, ∀ p < 32, (S j).getLsbD p = (Spec.Aes.sbox (bsByte Pl p)).getLsbD j)
    (h2 : ∀ i < 8, ∀ t < 32, (Out i).getLsbD t = (gConst32.getLsbD t ^^ xorBits S (l2w i t))) :
    ∀ w < 8, Out w = Spec.Seed.g (In w) := by
  -- The planes of `M`, and of the S-box.
  have hPl : ∀ p < 32, bsByte Pl p = linB mRows (byteW In (byteOf8 p)) := by
    intro p hp
    refine byte_ext fun j hj => ?_
    rw [Ct32.getLsbD_bsByte _ _ hj, h1 j hj p hp, getLsbD_linB _ _ hj, l1w,
      xorBits_byteW _ (rows_getD_lt (rows_lt mRows (by simp)) j)]
  have hSb : ∀ p < 32, bsByte S p = Spec.Aes.sbox (bsByte Pl p) := by
    intro p hp
    exact byte_ext fun j hj => by rw [Ct32.getLsbD_bsByte _ _ hj, hS j hj p hp]
  intro w hw
  apply BitVec.eq_of_getLsbD_eq
  intro t' ht'
  rw [h2 _ hw _ ht', show t' = 8 * (t' / 8) + t' % 8 by omega,
    getLsbD_g _ (by omega) (Nat.mod_lt _ (by omega)),
    gConst32_bits _ (by omega) _ (Nat.mod_lt _ (by omega))]
  -- The S-box outputs of byte `a`.
  have hbyte : ∀ a < 4, xorBits S
      (((pRows (a % 2 == 1)).getD (t' % 8) []).map fun j => 32 * j + laneOf8 (4 * w + a)) =
      (linB (pRows (a % 2 == 1)) (Spec.Aes.sbox (linB mRows (byteOf (In w) a)))).getLsbD
        (t' % 8) := by
    intro a ha
    have hn : 4 * w + a < 32 := by omega
    rw [xorBits_planesW _ (laneOf8_lt hn) (rows_getD_lt (pRows_lt _) _), hSb _ (laneOf8_lt hn),
      hPl _ (laneOf8_lt hn), byteOf8_laneOf8 hn, byteW_eq_byteOf _ ha,
      getLsbD_linB _ _ (Nat.mod_lt _ (by omega))]
  have hl2 : xorBits S (l2w w (8 * (t' / 8) + t' % 8)) =
      xor4 fun a => (maskOf ((a + t' / 8) % 4)).getLsbD (t' % 8) &&
        (linB (pRows (a % 2 == 1)) (Spec.Aes.sbox (linB mRows (byteOf (In w) a)))).getLsbD
          (t' % 8) := by
    have e1 : (8 * (t' / 8) + t' % 8) / 8 = t' / 8 := by omega
    have e2 : (8 * (t' / 8) + t' % 8) % 8 = t' % 8 := by omega
    rw [l2w, e1, e2, xorBits_range4_32]
    simp only [xor4, xorBits_ite32]
    rw [hbyte 0 (by omega), hbyte 1 (by omega), hbyte 2 (by omega), hbyte 3 (by omega)]
  rw [hl2]
  simp only [sOf, sbox_eq, BitVec.getLsbD_xor]
  rw [xor4_split, Bool.xor_comm]

end VG.Proof.Seed
