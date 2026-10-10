import VerifiedGarbage.Spec.Sm4

/-!
# Constants of the SM4 key schedule as bitsliced planes

The planes of `CK`'s words and `FK`'s words as the key schedule's code
stores them on every target, computed from the specification's constants.
-/

namespace VG.Impl.Sm4

/-- Plane `j` of the 32-bit word `x` in every block: bit `16 i + b` is bit
`j` of its byte `i`, from the most significant. -/
def planeOf (x : BitVec 32) (j : Nat) : BitVec 64 :=
  (BitVec.ofBoolListLE ((List.range 64).map fun p => x.getLsbD (8 * (3 - p / 16) + j))).setWidth 64

/-- `FK`'s words `2 h` and `2 h + 1` as a block stores them (each big-endian),
read as a little-endian word. -/
def fkWord (h : Nat) : BitVec 64 :=
  (BitVec.ofBoolListLE ((List.range 64).map fun t =>
    (Spec.Sm4.fk.getD (2 * h + t / 32) 0).getLsbD (8 * (3 - t % 32 / 8) + t % 8))).setWidth 64

/-- Plane `j` of the 32-bit word `x` in every block: bit `8 i + b` is bit
`j` of its byte `i`, from the most significant. -/
def planeOf32 (x : BitVec 32) (j : Nat) : BitVec 32 :=
  (BitVec.ofBoolListLE ((List.range 32).map fun p => x.getLsbD (8 * (3 - p / 8) + j))).setWidth 32

/-- `FK`'s word `w` as a block stores it (big-endian), read as a
little-endian word. -/
def fkLE (w : Nat) : BitVec 32 :=
  (BitVec.ofBoolListLE ((List.range 32).map fun t =>
    (Spec.Sm4.fk.getD w 0).getLsbD (8 * (3 - t / 8) + t % 8))).setWidth 32

end VG.Impl.Sm4
