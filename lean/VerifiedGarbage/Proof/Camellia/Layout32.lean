module

import VerifiedGarbage.Proof.Camellia.Layout
public import VerifiedGarbage.Proof.Camellia.Bitsliced32

/-!
# Bitsliced Camellia on 32-bit planes: words, bytes and blocks

The 32-bit targets load each block as four little-endian 32-bit words,
word `w` holding the block's bytes `4 w … 4 w + 3` (byte `i` of the word at
bits `8 i …`), and transpose the words `w` of eight blocks into the planes
of a half's word (`toBs`) and back (`fromBs`). `halves_of_words` and
`block_of_planes` turn what the transposes do to the bits into the halves
`D1` and `D2` of the blocks, and back. Nothing here depends on the target.
-/

@[expose] public section

namespace VG.Proof.Camellia.W32

open VG VG.Spec.Camellia

/-- Bit `8 i + j` of a little-endian 32-bit word is bit `j` of its byte `i`. -/
theorem readW32_bit (m : Mem) (a : Addr) {i j : Nat} (hi : i < 4) (hj : j < 8) :
    (m.readW a 32).getLsbD (8 * i + j) = (m (a + BitVec.ofNat 64 i)).getLsbD j := by
  rw [← Mem.extractLsb'_read m a (n := 4) hi, BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
  simp only [show 8 * i + j < 32 by omega, decide_true, Bool.true_and]

/-- The left half of a block. -/
abbrev hiOf (blk : Block) : BitVec 64 := (decodeBlock blk >>> 64).setWidth 64

/-- The right half of a block. -/
abbrev loOf (blk : Block) : BitVec 64 := (decodeBlock blk).setWidth 64

/-- The words `W` hold the blocks `B`: bit `8 (c % 4) + j` of word
`4 b + c / 4` is bit `j` of byte `c` of block `b`. -/
def BlockWords (W : Nat → BitVec 32) (B : Nat → Block) : Prop :=
  ∀ b < 8, ∀ c, (hc : c < 16) → ∀ j < 8, (W (4 * b + c / 4)).getLsbD (8 * (c % 4) + j) = ((B b)[c]'hc).getLsbD j

/-- The transpose: from the words of the eight blocks, plane `j` of word `w`
(of the sixteen planes of `D1`, then of `D2`) is bit `j` of byte `i` of
word `w` of block `b`, at `8 i + b`. -/
theorem halves_of_words {W Q : Nat → BitVec 32} {B : Nat → Block}
    (hT : ∀ w < 4, ∀ j < 8, ∀ p < 32, (Q (8 * w + j)).getLsbD p = (W (4 * (p % 8) + w)).getLsbD (8 * (p / 8) + j))
    (hW : BlockWords W B) :
    HalfRel Q (fun b => hiOf (B b)) ∧ HalfRel (fun k => Q (16 + k)) (fun b => loOf (B b)) := by
  constructor
  · intro b hb c hc j hj
    rw [hT (c / 4) (by omega) j hj _ (by omega), show (8 * (c % 4) + b) % 8 = b by omega,
      show (8 * (c % 4) + b) / 8 = c % 4 by omega, hW b hb c (by omega) j hj, byteOf_hi _ hc]
  · intro b hb c hc j hj
    have := hT (2 + c / 4) (by omega) j hj (8 * (c % 4) + b) (by omega)
    rw [show 8 * (2 + c / 4) + j = 16 + (8 * (c / 4) + j) by omega] at this
    rw [this, show (8 * (c % 4) + b) % 8 = b by omega,
      show (8 * (c % 4) + b) / 8 = c % 4 by omega, show 2 + c / 4 = (8 + c) / 4 by omega,
      show c % 4 = (8 + c) % 4 by omega, hW b hb (8 + c) (by omega) j hj, byteOf_lo _ hc]

/-- The transpose back: from the planes of the left half `hi` (the first
sixteen of `Q`) and the right half `lo` (the next sixteen), the words of
the blocks `hi ++ lo`. -/
theorem block_of_planes {W Q : Nat → BitVec 32} {hi lo : Nat → BitVec 64}
    (hF : ∀ b < 8, ∀ w < 4, ∀ i < 4, ∀ j < 8,
      (W (4 * b + w)).getLsbD (8 * i + j) = (Q (8 * w + j)).getLsbD (8 * i + b))
    (hH : HalfRel Q hi) (hL : HalfRel (fun k => Q (16 + k)) lo) :
    BlockWords W (fun b => encodeBlock (hi b ++ lo b)) := by
  intro b hb c hc j hj
  rw [hF b hb (c / 4) (by omega) (c % 4) (by omega) j hj, encodeBlock_getElem _ _ hc]
  split
  · rename_i h
    exact hH b hb c h j hj
  · rename_i h
    have := hL b hb (c - 8) (by omega) j hj
    dsimp only at this
    rw [show 16 + (8 * ((c - 8) / 4) + j) = 8 * (c / 4) + j by omega,
      show (c - 8) % 4 = c % 4 by omega] at this
    exact this

end VG.Proof.Camellia.W32
