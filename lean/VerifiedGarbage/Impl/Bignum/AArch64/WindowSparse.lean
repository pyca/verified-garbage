module

public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightRaw

/-! Initialize only the two holes left by each triangular tile, plus the
final padding. Every other product word is overwritten before its first read. -/

@[expose] public section
namespace VG.Impl.Bignum.AArch64.WindowSparse
open VG VG.AArch64 VG.Impl.Bignum.AArch64

def holes : List Instr := [st .x7 .x16, st .x7 .x16 120]
def rowHead (a : Nat) : List Instr :=
 ProductEight.outputPtr true a ++ (holes ++ SquareEight.code) ++
 [movi .x10 0] ++ ProductEight.outputPtr false a ++
 [ldh .x15 sW, .lsr .x .x15 .x15 3, .sub .x .x15 .x15 .x12]
def rows (a : Nat) : Prog isa :=
 .loop (.seq (.block (rowHead a))
  (.seq (.ite (.nonzero .x .x15) (countLoop .x15 ProductEight.offBlock) (.block []))
   (.block (SquareEightRaw.rowTail a)))) (.nonzero .x .x12)
def padding : List Instr :=
 [.lsl .x .x14 .x12 4, .add .x .x16 .x8 .x14, st .x7 .x16, st .x7 .x16 8]

end VG.Impl.Bignum.AArch64.WindowSparse
