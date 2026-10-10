import VerifiedGarbage.Spec.Sm4

/-!
# Constants of the SM4 key schedule as bitsliced planes

The planes of `CK`'s words and `FK`'s words as the key schedule's code
stores them on every target, computed from the specification's constants.
-/

namespace VG.Impl.Sm4

/-- The number whose bit `p < n` is `f p`, built with `Nat` operations,
which the kernel evaluates natively (unlike `BitVec.ofBoolListLE`). -/
def bitsOf (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => bitsOf f n ||| (if f n then 2 ^ n else 0)

/-- Plane `j` of the word `n`, `w` bits per byte of `n`: bits `w i … w i + w - 1`
are bit `j` of byte `i` of `n`, from the most significant. Four masks, which
the kernel evaluates in a few steps rather than bit by bit. -/
def planeBits (n w j : Nat) : Nat :=
  (if n.testBit (24 + j) then (2 ^ w - 1) <<< (0 * w) else 0) |||
    (if n.testBit (16 + j) then (2 ^ w - 1) <<< (1 * w) else 0) |||
    (if n.testBit (8 + j) then (2 ^ w - 1) <<< (2 * w) else 0) |||
    (if n.testBit j then (2 ^ w - 1) <<< (3 * w) else 0)

/-- Plane `j` of the 32-bit word `x` in every block: bit `16 i + b` is bit
`j` of its byte `i`, from the most significant. -/
def planeOf (x : BitVec 32) (j : Nat) : BitVec 64 := BitVec.ofNat 64 (planeBits x.toNat 16 j)

/-- `FK`'s words `2 h` and `2 h + 1` as a block stores them (each big-endian),
read as a little-endian word. -/
def fkWord (h : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (bitsOf (fun t =>
    (Spec.Sm4.fk.getD (2 * h + t / 32) 0).toNat.testBit (8 * (3 - t % 32 / 8) + t % 8)) 64)

/-- Plane `j` of the 32-bit word `x` in every block: bit `8 i + b` is bit
`j` of its byte `i`, from the most significant. -/
def planeOf32 (x : BitVec 32) (j : Nat) : BitVec 32 := BitVec.ofNat 32 (planeBits x.toNat 8 j)

/-- `FK`'s word `w` as a block stores it (big-endian), read as a
little-endian word. -/
def fkLE (w : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (bitsOf (fun t => (Spec.Sm4.fk.getD w 0).toNat.testBit (8 * (3 - t / 8) + t % 8)) 32)

end VG.Impl.Sm4
