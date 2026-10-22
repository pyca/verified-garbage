module

public import VerifiedGarbage.Impl.Argon2.AArch64.Instructions

/-! Write the compression result into the current matrix block. `x1` points
to the temporary result and `x0` to the matrix destination; `x5` is the public
pass number. Pass zero copies the result, and later passes XOR the old cell.
Both paths visit every pair of words in ascending order, in v0 and v1.
-/

@[expose] public section

namespace VG.Impl.Argon2.AArch64.FillWrite

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def pair (xorOld : Bool) (i : Nat) : List Instr :=
  .ldrq .v0 .x1 (16 * i) ::
    (if xorOld then [.ldrq .v1 .x0 (16 * i), .vop (.logic .eor .v0 .v0 .v1)] else []) ++
    [.strq .v0 .x0 (16 * i)]

def words (xorOld : Bool) (n : Nat) : List Instr := (List.range n).flatMap (pair xorOld)

def code : Prog isa := .seq (.block [comparei .x5 0].flatten)
  (.ite (.zero .x .x15) (.block (words false 64)) (.block (words true 64)))

end VG.Impl.Argon2.AArch64.FillWrite
