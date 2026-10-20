module

public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEight
public import VerifiedGarbage.Impl.Bignum.AArch64.ProductEight

@[expose] public section
namespace VG.Impl.Bignum.AArch64.SquareEightRaw
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

def carryWord (k : Nat) : List Instr :=
 [ld .x13 .x16 (8*(k+8)),
  (if k == 0 then Instr.adds else Instr.adcs) .x .x13 .x13 (if k == 0 then .x10 else .x7),
  st .x13 .x16 (8*(k+8))]
def finishCarry : List Instr := (List.range 7).flatMap carryWord

def rowHead (a : Nat) : List Instr :=
 ProductEight.outputPtr true a ++ SquareEight.code ++ [movi .x10 0] ++ ProductEight.outputPtr false a ++
   [ldh .x15 sW, .lsr .x .x15 .x15 3, .sub .x .x15 .x15 .x12]
def rowTail (a : Nat) : List Instr :=
 ProductEight.outputPtr true a ++ finishCarry ++ [.addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1]
def rows (a : Nat) : Prog isa :=
 .loop (.seq (.block (rowHead a))
   (.seq (.ite (.nonzero .x .x15) (countLoop .x15 ProductEight.offBlock) (.block []))
     (.block (rowTail a)))) (.nonzero .x .x12)
def raw (a : Nat) : Prog isa :=
 .seq (.block (Square.squareSetup a))
 (.seq WideLoops.zero
 (.seq (.block (ProductEight.saves ++ [ldh .x8 (sArr a), .lsr .x .x12 .x12 3]))
 (.seq (rows a) (.seq (.block (ProductEight.restores ++ Square.squareSetup a)) WideLoops.diagonal))))

def square (o a : Nat) : Prog isa :=
 .seq (raw a) (.seq (.block (BlockedRedc.saves o))
  (.seq BlockedRedc.redc (.seq (.block (BlockedRedc.restores o ++ Square.finishBases o))
    FastFinish.code)))

end VG.Impl.Bignum.AArch64.SquareEightRaw
