module

public import VerifiedGarbage.Impl.Rsa.Arm.RecoverScalar

/-! One pass over the full exponent, most significant byte first. A set
bit resets root detection; only the final trailing-zero chain survives.
The byte addresses and the choice of multiplication by a candidate depend
on public lengths and the permitted candidate count. -/

@[expose] public section
namespace VG.Impl.Rsa.Arm.RecoverFused
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover

/-- Outside the Montgomery kernel, exponent, and scalar scratch arrays. -/
def aRoot : Nat := 31

def sByte : Nat := 64
def sPtr : Nat := 68
def sBytes : Nat := 72
def sTmp : Nat := 76

/-- The next bit, without a branch on the exponent. -/
def bitHead : List Instr :=
  [.ldr .r1 .r8 sByte, .mov .r2 (.shifted .r1 .lsr 7),
    .dp .and .r2 .r2 (.imm 1), .str .r2 .r8 sBit,
    .mov .r1 (.shifted .r1 .lsl 1), .dp .and .r1 .r1 (.imm 255), .str .r1 .r8 sByte]

/-- Boolean header operations, with addresses fixed at code generation. -/
def flagNot (d a : Nat) : List Instr :=
  [.ldr .r1 .r8 a, .dp .eor .r1 .r1 (.imm 1), .str .r1 .r8 d]

def flagBin (isOr : Bool) (d a b : Nat) : List Instr :=
  [.ldr .r1 .r8 a, .ldr .r2 .r8 b,
    .dp (if isOr then .orr else .and) .r1 .r1 (.reg .r2), .str .r1 .r8 d]

/-- Record a root only on a zero bit; a set bit discards the old chain. -/
def hit : Prog isa := seqs [
  .block (flagNot sTmp sBit), .block (flagNot sLive sDone),
  .block (flagBin false sLive sLive sE1), .block (flagBin false sLive sLive sTmp),
  .block (flagBin true sOk sOk sLive), .block (flagBin false sOk sOk sTmp),
  .block (flagBin true sDone sDone sE1), .block (flagBin true sDone sDone sE2),
  .block (flagBin false sDone sDone sTmp)]

def candidateTest (v : Nat) : List Instr :=
  [.ldr .r1 .r8 sCand, .cmp .r1 (.imm (BitVec.ofNat 32 v))]

/-- Only candidates 2 and 3 use additions. Later candidates retain the
Montgomery product, including on UMAAL where it is substantially faster. -/
def multiply : Prog isa :=
  .seq (.block (candidateTest 0))
    (.ite .eq RecoverScalar.twice
      (.seq (.block (candidateTest 1))
        (.ite .eq RecoverScalar.three (seqs (mmul iXm iX iG)))))

/-- A set bit starts detection from the new value, after multiplication. -/
def tail : Prog isa := seqs [
  .block (flagBin true sLive sE1 sE2), .block (flagBin false sLive sLive sBit),
  .block (flagBin true sDone sDone sLive)]

def square : Prog isa := seqs [
  .block bitHead, seqs (mmul iX iY iY), eqAt sE1 mX aO, eqAt sE2 mX aNg, hit]

def save : Prog isa := .seq (sel aU aRoot aZ sBit) (sel aRoot aU mY sLive)

def value : Prog isa := .seq multiply (sel mY mX mXm sBit)

def finishBit : Prog isa := seqs [eqAt sE1 mY aO, eqAt sE2 mY aNg, tail]

def bit : Prog isa := seqs [square, save, value, finishBit]

/-- Start at the last byte of `ed - 1`; leading zero bytes are included. -/
def byteInitTail : List Instr := ptr .r0 wM ++
  [.dp .add .r1 .r1 (.reg .r2),
    .str .r1 .r8 sBytes, .dp .add .r0 .r0 (.reg .r1),
    .dp .sub .r0 .r0 (.imm 1), .str .r0 .r8 sPtr]

def byteInit : List Instr :=
  ctxW ++ [.ldrSp .r1 aoEl, .ldrSp .r2 aoDl] ++ byteInitTail ++ ctxw

def byteHead : List Instr :=
  [.ldr .r0 .r8 sPtr, .ldrb .r1 .r0 0, .str .r1 .r8 sByte]

def decrement (d : Nat) : List Instr :=
  [.ldr .r1 .r8 d, .subs .r1 .r1 (.imm 1), .str .r1 .r8 d]

def byteTail : List Instr := decrement sPtr ++ decrement sBytes

def byte : Prog isa := seqs [.block byteHead, seqs (List.replicate 8 bit), .block byteTail]

def constant (d v : Nat) : List Instr :=
  [.mov .r1 (.imm (BitVec.ofNat 32 v)), .str .r1 .r8 d]

def initFlags : List Instr := constant sDone 1 ++ constant sOk 0 ++ constant sByte 0

def init : Prog isa := seqs [copy mG aZ,
  .block (ptr .r0 mG ++ [.ldr .r1 .r8 sCand, .dp .add .r1 .r1 (.imm 2), .str .r1 .r0 0]),
  seqs (mmul iG iG iR2), copy mY aO, copy aRoot aZ,
  .block initFlags,
  .block byteInit]

def candidate : Prog isa := seqs [init, .loop byte .ne, copy mY aRoot, .block candNext]

def candidates : Prog isa :=
  .seq (.block [.mov .r1 (.imm 0), .str .r1 .r8 sCand]) (.loop candidate .ne)

/-- The fused search scans the full exponent and needs no preliminary
halving. Reuse Montgomery setup and factor extraction directly. -/
def rest : Prog isa := seqs [mont, candidates, fin]

def valid : Prog isa := .seq numbers (.ite .eq rest fail)

def body : Prog isa := .ite .eq valid fail

def code : Prog isa := Recover.codeWith body

end VG.Impl.Rsa.Arm.RecoverFused
