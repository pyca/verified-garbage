module
public import VerifiedGarbage.Impl.Bignum.AArch64.Core


/-! Double the cross-product stream and add diagonal squares with one carry
chain. The preceding undoubled high word carries the shift bit separately
from the addition carry flag. -/

@[expose] public section
namespace VG.Impl.Bignum.AArch64.DiagonalChain
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

def head (i : Nat) : List Instr :=
 [ld .x1 .x11 (8*i), .mul .x .x2 .x1 .x1, .umulh .x1 .x1 .x1,
  ld .x3 .x16 (16*i), ld .x4 .x16 (16*i+8)]

def core : List Instr :=
 [.extr .x .x6 .x4 .x3 63, .extr .x .x3 .x3 .x5 63,
  mov .x5 .x4, .adcs .x .x3 .x3 .x2, .adcs .x .x6 .x6 .x1]

def tail (i : Nat) : List Instr :=
 [st .x3 .x16 (16*i), st .x6 .x16 (16*i+8)]

def step (i : Nat) : List Instr := head i ++ core ++ tail i

def code : Prog isa :=
 .seq (.block [mov .x16 .x8, mov .x11 .x9, .lsr .x .x14 .x12 2,
   .adds .x .x5 .x7 .x7])
 (.seq (countLoop .x14 ((List.range 4).flatMap step ++
   [.addImm .x .x16 .x16 64, .addImm .x .x11 .x11 32]))
  (.block [.lsr .x .x5 .x5 63, .adc .x .x5 .x5 .x7, st .x5 .x16]))

end VG.Impl.Bignum.AArch64.DiagonalChain
