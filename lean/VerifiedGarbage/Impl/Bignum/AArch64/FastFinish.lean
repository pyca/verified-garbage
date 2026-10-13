module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! Four-limb canonical subtraction and selection for widths divisible by four. -/

@[expose] public section
namespace VG.Impl.Bignum.AArch64.FastFinish
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
def subWord (i : Nat) : List Instr :=
  [ld .x3 .x16 (8*i), ld .x4 .x17 (8*i), .sbcs .x .x3 .x3 .x4, st .x3 .x13 (8*i)]
def sub4 : List Instr := (List.range 4).flatMap subWord
def sub : Prog isa :=
  .seq (.block [mov .x16 .x8, mov .x17 .x10, mov .x13 .x6,
    .lsr .x .x14 .x12 2, .subs .x .x3 .x7 .x7])
  (.seq (countLoop .x14 (sub4 ++ [.addImm .x .x16 .x16 32,
    .addImm .x .x17 .x17 32, .addImm .x .x13 .x13 32]))
    (.block [ld .x3 .x16, .sbcs .x .x3 .x3 .x7]))
def selWord (i : Nat) : List Instr :=
  [ld .x3 .x16 (8*i), ld .x4 .x6 (8*i), .csel .x .x3 .x4 .x3, st .x3 .x5 (8*i)]
def sel4 : List Instr := (List.range 4).flatMap selWord
def sel : Prog isa := .seq (.block [mov .x16 .x8, .lsr .x .x14 .x12 2])
  (countLoop .x14 (sel4 ++ [.addImm .x .x16 .x16 32, .addImm .x .x6 .x6 32, .addImm .x .x5 .x5 32]))
def code : Prog isa := .seq sub sel
end VG.Impl.Bignum.AArch64.FastFinish
