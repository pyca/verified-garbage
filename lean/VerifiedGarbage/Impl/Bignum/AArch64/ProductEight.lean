module

public import VerifiedGarbage.Impl.Bignum.AArch64.WideLoops
public import VerifiedGarbage.Impl.Bignum.AArch64.FastFinish
public import VerifiedGarbage.Impl.Bignum.AArch64.BlockedRedc

@[expose] public section

namespace VG.Impl.Bignum.AArch64.ProductEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
def regs : List Reg := BlockedRedc.saved
def vecs : List VReg := [.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23,.v24,.v25,.v26]
def saves : List Instr := (regs.zip vecs).map fun (r,v) => .vop (.ins .d2 v 0 r)
def restores : List Instr := (regs.zip vecs).map fun (r,v) => .umov .x r v 0
-- x8 is the advancing input pointer, x16 the corresponding product pointer.
def outputPtr (twice : Bool) (a : Nat) : List Instr :=
 [ldh .x17 (sArr a), .sub .x .x16 .x8 .x17] ++
 (if twice then [.lsl .x .x16 .x16 1] else []) ++
 [ldh .x13 (sArr Public.aAcc), .addImm .x .x13 .x13 16, .add .x .x16 .x16 .x13]
def offBlock : List Instr :=
 (BlockedRedc.aa.zipIdx.map fun (r,i) => ld r .x16 (8*i)) ++ BlockedRedc.nsLoad ++
 [.adds .x .x1 .x7 .x7] ++ (List.range 8).flatMap BlockedRedc.tail ++
 BlockedRedc.addMemory true ++ [.adc .x .x10 .x7 .x7] ++ BlockedRedc.asStore ++
 [.addImm .x .x17 .x17 64]
def rowSetup (a b : Nat) : List Instr :=
 outputPtr false a ++ [ldh .x17 (sArr b), ldh .x15 sW,
   .lsr .x .x15 .x15 3, movi .x10 0]
def rows (a b : Nat) : Prog isa :=
 .loop (.seq (.block (rowSetup a b))
   (.seq (countLoop .x15 offBlock)
    (.block [.addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1]))) (.nonzero .x .x12)
def raw (a b : Nat) : Prog isa :=
 .seq (.block (Square.squareSetup a))
 (.seq WideLoops.zero
 (.seq (.block (saves ++ [ldh .x8 (sArr a), .lsr .x .x12 .x12 3]))
 (.seq (rows a b) (.block (restores ++ Square.squareSetup a)))))

def multiply (o a b : Nat) : Prog isa :=
 .seq (raw a b) (.seq (.block (BlockedRedc.saves o))
  (.seq BlockedRedc.redc (.seq (.block (BlockedRedc.restores o ++ Square.finishBases o))
    FastFinish.code)))

end VG.Impl.Bignum.AArch64.ProductEight
