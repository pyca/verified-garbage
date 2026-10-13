module

public import VerifiedGarbage.Impl.Bignum.AArch64.BlockedRedc

@[expose] public section

namespace VG.Impl.Bignum.AArch64.WideLoops
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
def zero : Prog isa :=
 .seq (.block [mov .x16 .x8, .add .x .x14 .x12 .x12, .lsr .x .x14 .x14 3])
 (.seq (countLoop .x14 ((List.range 8).map (fun i => st .x7 .x16 (8*i)) ++ [.addImm .x .x16 .x16 64]))
  (.block [st .x7 .x16, st .x7 .x16 8]))
end VG.Impl.Bignum.AArch64.WideLoops

namespace VG.Impl.Bignum.AArch64.WideLoops
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
def step (i : Nat) : List Instr :=
 [ld .x1 .x11 (8*i), .mul .x .x2 .x1 .x1, .umulh .x1 .x1 .x1,
  ld .x3 .x16 (16*i), ld .x4 .x16 (16*i+8)] ++ Square.diagonalCore ++
 [st .x3 .x16 (16*i), st .x4 .x16 (16*i+8)]
def diagonal : Prog isa :=
 .seq (.block [mov .x16 .x8, mov .x11 .x9, .lsr .x .x14 .x12 2, movi .x5 0])
 (.seq (countLoop .x14 ((List.range 4).flatMap step ++ [.addImm .x .x16 .x16 64,
    .addImm .x .x11 .x11 32])) (.block [st .x5 .x16]))
end VG.Impl.Bignum.AArch64.WideLoops
