import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
import VerifiedGarbage.TCB.X86.Print
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Impl.Rsa.X86.Keys (seqs)
namespace SquareProto
-- Scratch, unproven: product scanning with independent 64-bit sums.
def accum : List Instr := [
  .mop (.movd .mm2 .eax), .mop (.bin .paddq .mm0 (.reg .mm2)),
  .mop (.movd .mm2 .edx), .mop (.bin .paddq .mm1 (.reg .mm2))]
def prod : List Instr := [.mov .eax (.mem (at_ .ecx 0)),
  .mov .edx (.mem (at_ .ebp 0)), .mul .edx] ++ accum

def pairLoop : Prog isa := .loop (.block (prod ++ [
  .alu .add .ecx (.imm 4), .alu .sub .ebp (.imm 4), .alu .cmp .ecx (.reg .ebp)])) .b

def cross : Prog isa := seqs [
  .block (lenTimes .eax 0 ++ [.mov .edx (.reg .esi), .alu .add .edx (.imm 4), .alu .sub .edx (.reg .eax)]),
  .ite .b (.block [.mov .edx (.imm 0)]) (.block []),
  .block [.mov .ecx (.mem argWs), .mov .eax (.mem argA), .alu .add .ecx (.reg .eax),
    .mov .ebp (.reg .ecx), .alu .add .ecx (.reg .edx),
    .alu .add .ebp (.reg .esi), .alu .sub .ebp (.reg .edx), .alu .cmp .ecx (.reg .ebp)],
  .ite .b pairLoop (.block []),
  .block [.mop (.shift .psllq .mm0 1), .mop (.shift .psllq .mm1 1),
    .mov .eax (.reg .esi), .alu .and .eax (.imm 4)],
  .ite .e (.block ([.mov .eax (.reg .esi), .shift .shr .eax 1,
    .mov .edx (.mem argWs), .alu .add .eax (.reg .edx), .mov .edx (.mem argA),
    .alu .add .eax (.reg .edx), .mov .eax (.mem (at_ .eax 0)), .mul .eax] ++ accum)) (.block [])]

def carryIn : List Instr := [
  .mop (.movq .mm2 (.reg .mm3)), .mop (.bin .pand .mm2 (.reg .mm7)),
  .mop (.bin .paddq .mm0 (.reg .mm2)), .mop (.shift .psrlq .mm3 32),
  .mop (.bin .paddq .mm1 (.reg .mm3))]

def redLoop : Prog isa := .loop (.block (prod ++ [
  .alu .add .ecx (.imm 4), .alu .sub .ebp (.imm 4), .alu .cmp .ecx (.reg .ebx)])) .b

def reduction : Prog isa := seqs [
  .block (lenTimes .ebx 0 ++ [.mov .edx (.reg .esi), .alu .add .edx (.imm 4), .alu .sub .edx (.reg .ebx)]),
  .ite .b (.block [.mov .edx (.imm 0)]) (.block []),
  .block [.mov .ecx (.reg .edi), .alu .add .ecx (.imm 52), .alu .add .ecx (.reg .edx),
    .mov .ebp (.mem argWs), .mov .eax (.mem argM), .alu .add .ebp (.reg .eax),
    .alu .add .ebp (.reg .esi), .alu .sub .ebp (.reg .edx),
    .alu .cmp .esi (.reg .ebx)],
  .ite .b (.block [.mov .ebx (.reg .esi)]) (.block []),
  .block [.alu .add .ebx (.reg .edi), .alu .add .ebx (.imm 52), .alu .cmp .ecx (.reg .ebx)],
  .ite .b redLoop (.block []),
  .block ([.mmxStore (sc 20) .mm0] ++ lenTimes .eax 0 ++ [.alu .cmp .esi (.reg .eax)]),
  .ite .b
    (.block (ptr .edx argInv .eax ++ [.mov .edx (.mem (at_ .edx 0)),
      .mov .eax (.mem (sc 20)), .mul .edx,
      .mov .ecx (.reg .edi), .alu .add .ecx (.imm 52), .alu .add .ecx (.reg .esi),
      .store (at_ .ecx 0) .eax, .mov .ebx (.reg .eax)] ++ ptr .ebp argM .edx ++
      [.mov .eax (.mem (at_ .ebp 0)), .mul .ebx] ++ accum))
    (.block [.mov .eax (.mem (sc 20)), .mov .ecx (.reg .edi),
      .alu .add .ecx (.imm 52), .alu .add .ecx (.reg .esi), .store (at_ .ecx 0) .eax])]

def column : Prog isa := seqs [
  .block [.mop (.bin .pxor .mm0 (.reg .mm0)), .mop (.bin .pxor .mm1 (.reg .mm1))],
  cross, .block carryIn, reduction,
  .block ([.mop (.movq .mm3 (.reg .mm0)), .mop (.shift .psrlq .mm3 32),
    .mop (.bin .paddq .mm3 (.reg .mm1)), .alu .add .esi (.imm 4)] ++
    lenTimes .eax 1 ++ [.alu .cmp .esi (.reg .eax)])]

def columns : Prog isa := seqs [
  .block [.mov .esi (.imm 0), .mop (.bin .pxor .mm3 (.reg .mm3)),
    .mov .eax (.imm (-1)), .mop (.movd .mm7 .eax)],
  .loop column .ne,
  .block ([.mov .ebp (.reg .edi), .alu .add .ebp (.imm 52), .alu .add .ebp (.reg .esi),
    .mmxStore (at_ .ebp 0) .mm3] ++ lenTimes .eax 0 ++ [.alu .sub .ebp (.reg .eax)])]

def square : Prog isa := seqs [.block save, .frame .mmxEnter columns .emms,
  subM, .block mask, select, .block restoreRegs]

def dispatch : Prog isa := .seq (.block [.mov .eax (.mem argA), .alu .cmp .eax (.mem argB)])
  (.ite .e square VG.Impl.Mont.X86.Rt.body)

def printFn (name : String) (p : Prog isa) (callee : String := "proto_mont") : String :=
  ".globl " ++ name ++ "\n.p2align 6\n" ++ name ++ ":\n" ++
  "\n".intercalate ((printer.function p).map fun l => match l with
    | .text s => s | .call _ => "call " ++ callee | .sym .. => "ERROR") ++ "\n"
end SquareProto

namespace SseProto
-- Scratch, unproven: product scanning with independent 64-bit sums.
def accum : List Instr := [
  .xop (.movd .xmm2 .eax), .xop (.bin .paddq .xmm0 (.xmm2)),
  .xop (.movd .xmm2 .edx), .xop (.bin .paddq .xmm1 (.xmm2))]
def prod : List Instr := [.mov .eax (.mem (at_ .ecx 0)),
  .mov .edx (.mem (at_ .ebp 0)), .mul .edx] ++ accum

def pairLoop : Prog isa := .loop (.block (prod ++ [
  .alu .add .ecx (.imm 4), .alu .sub .ebp (.imm 4), .alu .cmp .ecx (.reg .ebp)])) .b

def cross : Prog isa := seqs [
  .block (lenTimes .eax 0 ++ [.mov .edx (.reg .esi), .alu .add .edx (.imm 4), .alu .sub .edx (.reg .eax)]),
  .ite .b (.block [.mov .edx (.imm 0)]) (.block []),
  .block [.mov .ecx (.mem argWs), .mov .eax (.mem argA), .alu .add .ecx (.reg .eax),
    .mov .ebp (.reg .ecx), .alu .add .ecx (.reg .edx),
    .alu .add .ebp (.reg .esi), .alu .sub .ebp (.reg .edx), .alu .cmp .ecx (.reg .ebp)],
  .ite .b pairLoop (.block []),
  .block [.xop (.shift .psllq .xmm0 1), .xop (.shift .psllq .xmm1 1),
    .mov .eax (.reg .esi), .alu .and .eax (.imm 4)],
  .ite .e (.block ([.mov .eax (.reg .esi), .shift .shr .eax 1,
    .mov .edx (.mem argWs), .alu .add .eax (.reg .edx), .mov .edx (.mem argA),
    .alu .add .eax (.reg .edx), .mov .eax (.mem (at_ .eax 0)), .mul .eax] ++ accum)) (.block [])]

def carryIn : List Instr := [
  .xop (.bin .movdqa .xmm2 (.xmm3)), .xop (.bin .pand .xmm2 (.xmm7)),
  .xop (.bin .paddq .xmm0 (.xmm2)), .xop (.shift .psrlq .xmm3 32),
  .xop (.bin .paddq .xmm1 (.xmm3))]

def redLoop : Prog isa := .loop (.block (prod ++ [
  .alu .add .ecx (.imm 4), .alu .sub .ebp (.imm 4), .alu .cmp .ecx (.reg .ebx)])) .b

def reduction : Prog isa := seqs [
  .block (lenTimes .ebx 0 ++ [.mov .edx (.reg .esi), .alu .add .edx (.imm 4), .alu .sub .edx (.reg .ebx)]),
  .ite .b (.block [.mov .edx (.imm 0)]) (.block []),
  .block [.mov .ecx (.reg .edi), .alu .add .ecx (.imm 52), .alu .add .ecx (.reg .edx),
    .mov .ebp (.mem argWs), .mov .eax (.mem argM), .alu .add .ebp (.reg .eax),
    .alu .add .ebp (.reg .esi), .alu .sub .ebp (.reg .edx),
    .alu .cmp .esi (.reg .ebx)],
  .ite .b (.block [.mov .ebx (.reg .esi)]) (.block []),
  .block [.alu .add .ebx (.reg .edi), .alu .add .ebx (.imm 52), .alu .cmp .ecx (.reg .ebx)],
  .ite .b redLoop (.block []),
  .block ([.movqStore (sc 20) .xmm0] ++ lenTimes .eax 0 ++ [.alu .cmp .esi (.reg .eax)]),
  .ite .b
    (.block (ptr .edx argInv .eax ++ [.mov .edx (.mem (at_ .edx 0)),
      .mov .eax (.mem (sc 20)), .mul .edx,
      .mov .ecx (.reg .edi), .alu .add .ecx (.imm 52), .alu .add .ecx (.reg .esi),
      .store (at_ .ecx 0) .eax, .mov .ebx (.reg .eax)] ++ ptr .ebp argM .edx ++
      [.mov .eax (.mem (at_ .ebp 0)), .mul .ebx] ++ accum))
    (.block [.mov .eax (.mem (sc 20)), .mov .ecx (.reg .edi),
      .alu .add .ecx (.imm 52), .alu .add .ecx (.reg .esi), .store (at_ .ecx 0) .eax])]

def column : Prog isa := seqs [
  .block [.xop (.bin .pxor .xmm0 (.xmm0)), .xop (.bin .pxor .xmm1 (.xmm1))],
  cross, .block carryIn, reduction,
  .block ([.xop (.bin .movdqa .xmm3 (.xmm0)), .xop (.shift .psrlq .xmm3 32),
    .xop (.bin .paddq .xmm3 (.xmm1)), .alu .add .esi (.imm 4)] ++
    lenTimes .eax 1 ++ [.alu .cmp .esi (.reg .eax)])]

def columns : Prog isa := seqs [
  .block [.mov .esi (.imm 0), .xop (.bin .pxor .xmm3 (.xmm3)),
    .mov .eax (.imm (-1)), .xop (.movd .xmm7 .eax)],
  .loop column .ne,
  .block ([.mov .ebp (.reg .edi), .alu .add .ebp (.imm 52), .alu .add .ebp (.reg .esi),
    .movqStore (at_ .ebp 0) .xmm3] ++ lenTimes .eax 0 ++ [.alu .sub .ebp (.reg .eax)])]

def square : Prog isa := seqs [.block save, columns,
  subM, .block mask, select, .block restoreRegs]

def dispatch : Prog isa := .seq (.block [.mov .eax (.mem argA), .alu .cmp .eax (.mem argB)])
  (.ite .e square VG.Impl.Mont.X86.Rt.body)

def printFn (name : String) (p : Prog isa) (callee : String := "proto_mont") : String :=
  ".globl " ++ name ++ "\n.p2align 6\n" ++ name ++ ":\n" ++
  "\n".intercalate ((printer.function p).map fun l => match l with
    | .text s => s | .call _ => "call " ++ callee | .sym .. => "ERROR") ++ "\n"
end SseProto

namespace GcdProto
open VG.Impl.Rsa.X86.Keys (sOdd sB sC aT1 aT2 aT3)
open VG.Impl.Rsa.X86.Recover VG.Impl.Rsa.X86.RecoverRt
open VG.Impl.Rsa.X86.KeyRt

def step (A D : Nat) : Prog isa := seqs [
  .block (bitOf nar sOdd A), sub3 nar aT1 A (A+1),
  .block ([.store (sc sB) .ebx] ++ VG.Impl.Rsa.X86.Keys.andS sC sOdd sB),
  sub3 nar aT2 (A+1) A, sel nar (D+1) (A+1) A sC,
  sel nar aT3 aT1 aT2 sC, sel nar D A aT3 sOdd,
  .block [.mov .ebx (.imm 0)], half nar D]

def gcd : Prog isa := .seq (.block (bits nar))
  (.loop (seqs [step 0 4,step 4 0,.block [.alu .sub .esi (.imm 1),.alu .cmp .esi (.imm 0)]]) .ne)

def finGcd : Prog isa := seqs [finY,gcdSet,gcd,divSet,VG.Impl.Rsa.X86.KeyRt.div nar aQ aRm aDv aDt,order,stores]
def selected : Prog isa := .seq (.block recoveryChoice) (.iteCold .b
  (seqs [halving,mont,candLoop,finGcd]) (seqs [fusedPrepare,mont,fusedLoop,finGcd]))
def code : Prog isa := seqs [.block entry,.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 4),
  .block VG.Impl.Bignum.X86.modulusCheck,
  .ite .e (.seq numbers (.ite .e selected failure)) failure,.block VG.Impl.Bignum.X86.PublicFn.restore]
end GcdProto

namespace FastAdd
open VG.Impl.Rsa.X86.KeyRt
open VG.Impl.Rsa.X86.Keys (sC)
def addMod (L : Lay) (o a b m z t : Nat) : List (Prog isa) :=
  [chain L .adc (t+1) a b false, sub3 L (t+2) (t+1) m,
   .block [.store (sc sC) .ebx], sel L o (t+2) (t+1) sC]
end FastAdd

namespace FastAddProto
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.Keys (aM aNM aZero hdr seqs)
open VG.Impl.Rsa.X86.KeyRt (Lay Shape arrPtr bytesB sub3 copy sel half bitOf setOne clrLow eqSFast zeroArrays
  mulMod gcd div load restoreEdi)
open VG.Impl.Rsa.X86.Recover (sTc sCand sK sDone sOk sBit sLive sE1 sE2 sCnt sLt sInv sMask sWin sEq mAcc
  mBase mY mR2 mG mXm mX aN aOne aZ aO aNg aW aQ aRm aDv aDt nArr wZ wE wD wM wMod wT wH wR wRc
  entry skipTest cntBits cntNext sqInit sqMasks sqNext candNext prodCount windowCount)

/-- The modulus's length (argument 5) and the working space (argument 10), with `k` words pushed. -/
def lay (shape : Shape) (k : Nat := 0) : Lay := { len := 5 + k, ws := 10 + k, shape }

/-- The numbers modulo `n`. -/
abbrev nar : Lay := lay .narrow
/-- The product and its halvings. -/
abbrev wid : Lay := lay .wide

/-- Narrow array `j`'s wide index: `2 j`. -/
def w (j : Nat) : Nat := 2 * j

/-! ## The numbers -/

def loads : Prog isa := seqs [zeroArrays nar nArr, load nar 4 aN, load nar 6 (w wE), load nar 8 (w wD)]

/-- The top bit of the wide `[wMod]`: the modulus `2^(32 W - 1)` of the product. -/
def setTop : List Instr :=
  arrPtr wid .eax wMod .edx ++ [.alu .add .eax (.reg .edx), .alu .sub .eax (.imm 12),
    .mov .ecx (.imm 0x80000000), .store (at_ .eax 0) .ecx]

def prod : Prog isa := .seq (.block (setTop ++ prodCount)) (mulMod wid wZ wE wD wM wMod wT)

def skipBits : List Instr := bitOf wid sBit wM ++ clrLow wid wM

def numbers : Prog isa := seqs [loads, prod, .block skipBits, sub3 wid wT wZ wM, .block skipTest]

/-! ## The halvings of `e d - 1` -/

def halfInit : Prog isa := seqs [copy wid wR wM,
  .block ([.mov .eax (.imm 0), .store (sc sTc) .eax] ++ cntBits)]

def halfBit : List Instr := bitOf wid sBit wR ++ [
  .mov .eax (.mem (sc sBit)), .alu .xor .eax (.imm 1), .store (sc sBit) .eax,
  .mov .edx (.mem (sc sTc)), .alu .add .edx (.reg .eax), .store (sc sTc) .edx]

/-- Keep the old value in `wR` until the masked update; no snapshot array is needed. -/
def halfBody : Prog isa := seqs [copy wid wH wR,
  .block [.mov .ebx (.imm 0)], half wid wH, .block halfBit,
  sel wid wR wR wH sBit, .block cntNext]

def halving : Prog isa := .seq halfInit (.loop halfBody .ne)

/-! ## Montgomery arithmetic modulo `n` -/

/-- The narrow arrays with the 36 bytes of a call's frame pushed. -/
abbrev narF : Lay := lay .narrow 9

/-- `eax` the offset of narrow array `j`, from `edx` its stride. -/
def offIn (j : Nat) : List Instr :=
  .mov .eax (.imm (BitVec.ofNat 32 hdr)) :: List.replicate j (.alu .add .eax (.reg .edx))

/-- The arguments of `vg_rsa_mont_mul_at` for the narrow arrays `o`, `a` and `b`, into the frame at
`esp`: `ws` (`edi`), `ws_len` (argument 11), the width `B / 8`, the modulus (`mBase`), the inverse
(`sInv`), the callee's range (`mAcc`, four arrays), `o`, `a` and `b`. -/
def mulArgs (o a b : Nat) : List Instr :=
  bytesB narF .edx ++
    [.mov .eax (.mem (PublicRt.argAt 9 11)), .store (at_ .esp 4) .eax, .store (at_ .esp 0) .edi,
      .mov .eax (.reg .edx), .alu .sub .eax (.imm 8), .shift .shr .eax 3, .store (at_ .esp 8) .eax,
      .alu .add .edx (.imm 8)] ++
    offIn mBase ++ [.store (at_ .esp 12) .eax, .mov .eax (.imm (BitVec.ofNat 32 sInv)), .store (at_ .esp 16) .eax] ++
    offIn mAcc ++ [.store (at_ .esp 20) .eax] ++ offIn o ++ [.store (at_ .esp 24) .eax] ++
    offIn a ++ [.store (at_ .esp 28) .eax] ++ offIn b ++ [.store (at_ .esp 32) .eax]

/-- The two words of narrow array `j` above its `B` bytes zeroed. -/
def clrTop (j : Nat) : List Instr :=
  arrPtr nar .eax j .edx ++ [.alu .add .eax (.reg .edx), .alu .sub .eax (.imm 16), .mov .ecx (.imm 0),
    .store (at_ .eax 0) .ecx, .store (at_ .eax 4) .ecx]

/-- `[o] = [a] [b] R⁻¹ mod n`, `R = 2^(8 B)`, by a call of `vg_rsa_mont_mul_at` in a frame of 36
bytes, which keeps `ebx`, `esi`, `ebp` and `edi`; then `[o]`'s top words zeroed. -/
def mmul (o a b : Nat) : Prog isa :=
  .seq (.frame (.alloc 36) (.seq (.block (mulArgs o a b)) (.call Spec.Rsa.MontMul.mulApi.name Rt.body)) (.free 36))
    (.block (clrTop o))

/-- `-n⁻¹ mod 2³²` from `[mBase]`'s low word. -/
def setupInverse : List Instr :=
  arrPtr nar .eax mBase .edx ++ [.mov .ebx (.mem (at_ .eax 0))] ++ Dynamic.inverse ++ [.store (sc sInv) .eax]

/-- `[mR2] = R² mod n`: one, doubled `16 B` times modulo `n` through the callee's range (`mAcc` to
`mAcc + 2`), with `[aZ]` zero. -/
def setupR2 : Prog isa := seqs [copy nar mR2 aOne,
  .block (bytesB nar .esi ++ [.alu .sub .esi (.imm 8), .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi),
    .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi)]),
  .loop (seqs (FastAdd.addMod nar mR2 mR2 mR2 aN aZ mAcc ++
    [.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]])) .ne]

/-- Zero, one, the modulus, its inverse and `R²`, and one into `mXm`. -/
def montHead : Prog isa := seqs [
  sub3 nar aZ aN aN, copy nar aOne aZ, .block (setOne nar aOne),
  copy nar mBase aN, .block setupInverse,
  setupR2, copy nar mXm aOne]

/-- `R mod n` into `aO`, and `n - R mod n` into `aNg`. -/
def montTail : Prog isa := seqs [copy nar aO mXm, sub3 nar aNg aN aO]

def mont : Prog isa := seqs [montHead, mmul mXm mXm mR2, montTail]

/-! ## The candidates -/

def candSet : Prog isa := seqs [copy nar mG aZ,
  .block ([.mov .ecx (.mem (sc sCand)), .alu .add .ecx (.imm 2)] ++ arrPtr nar .eax mG .edx ++
    [.store (at_ .eax 0) .ecx]),
  copy nar mY aO, copy wid wRc wR]

/-- `32 W / 4 - c / 4`, the four-bit shifts that put the exponent's top window at the top of its
`W` words, `c = 8 (e_len + d_len)`. -/
def alignCount : List Instr := [.mov .eax (.mem (PublicFn.argument 7)),
  .alu .add .eax (.mem (PublicFn.argument 9)), .alu .add .eax (.reg .eax)] ++ bytesB wid .edx ++
  [.alu .add .edx (.reg .edx), .alu .sub .edx (.reg .eax), .store (sc sCnt) .edx]

/-- The wide `[wRc]` shifted up by four bits. -/
def shiftUp : Prog isa :=
  .seq (.block (arrPtr wid .ebp wRc .edx ++ bytesB wid .edx ++ [.mov .ecx (.imm 0)])) CrtRt.shiftLoop

def alignBody : Prog isa := .seq shiftUp (.block cntNext)

def alignStart : Prog isa := .seq candSet (.block alignCount)

/-- The table of the candidate's powers `0` to `15` (Montgomery form) in narrow arrays `0` to `15`. -/
def tableStep (i : Nat) : Prog isa := .seq (mmul mXm mXm mG) (copy nar (i + 2) mXm)

/-- The first `k` steps of the table. -/
def tableSteps : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq (tableSteps k) (tableStep k)

def tableStart : Prog isa := seqs [copy nar 0 aO, copy nar 1 mG, copy nar mXm mG]

def table : Prog isa := .seq tableStart (tableSteps 14)

/-- The exponent's top four bits, into `sWin`. -/
def windowTop : List Instr :=
  arrPtr wid .eax wRc .edx ++ [.alu .add .eax (.reg .edx), .alu .sub .eax (.imm 12), .mov .eax (.mem (at_ .eax 0)),
    .shift .shr .eax 28, .store (sc sWin) .eax]

/-- The window's entry into `mXm`, by a scan of entries `0` to `k`. -/
def scan : Nat → Prog isa
  | 0 => copy nar mXm 0
  | k + 1 => seqs [scan k, .block (VG.Impl.Rsa.X86.Recover.windowIs (k + 1)), sel nar mXm mXm (k + 1) sEq]

def square : Prog isa := mmul mY mY mY

/-- The window, the exponent shifted past it, and its table entry into `mXm`. -/
def windowNext : Prog isa := seqs [.block windowTop, shiftUp, scan 15]

def windowBody : Prog isa := seqs [square, square, square, square,
  windowNext, mmul mY mY mXm, .block cntNext]

def eqAt (d a b : Nat) : Prog isa := eqSFast nar d a b

/-- The square's tests and masks, and `mY` kept or replaced by it. -/
def sqTail : Prog isa := seqs [eqAt sE1 mX aO, eqAt sE2 mX aNg, .block sqMasks,
  sel nar mY mY mX sLive, .block sqNext]

def sqBody : Prog isa := .seq (mmul mX mY mY) sqTail

def candExp : Prog isa := seqs [alignStart, .loop alignBody .ne,
  mmul mG mG mR2, table, .block windowCount, .loop windowBody .ne]

def candSquareInit : Prog isa := seqs [eqAt sE1 mY aO, eqAt sE2 mY aNg, .block sqInit]

def candSquare : Prog isa := .seq candSquareInit (.loop sqBody .ne)

def candBody : Prog isa := seqs [candExp, candSquare, .block candNext]

def candLoop : Prog isa := .seq
  (.block [.mov .eax (.imm 0), .store (sc sCand) .eax]) (.loop candBody .ne)

/-! ## The factors -/

def finHead : Prog isa := seqs [
  .block [.mov .eax (.mem (sc sOk)), .store (sc sMask) .eax], copy nar mXm aOne]

def finY : Prog isa := .seq finHead (mmul mY mY mXm)

def gcdSet : Prog isa := seqs [sub3 nar 0 mY aOne,
  copy nar 1 aN, copy nar aM aN, copy nar 2 aZ,
  .block (setOne nar 2), copy nar 3 aZ, copy nar aZero aZ,
  sub3 nar aNM aZero aM]

/-- The dividend `n` and the divisor, with the word above the divisor's zeroed. -/
def divSet : Prog isa := seqs [copy nar aQ aN, copy nar aDv 1,
  .block (arrPtr nar .eax aDv .edx ++ [.alu .add .eax (.reg .edx), .alu .sub .eax (.imm 8), .mov .ecx (.imm 0),
    .store (at_ .eax 0) .ecx])]

def order : Prog isa := seqs [sub3 nar aW 1 aQ,
  .block [.store (sc sLt) .ebx], sel nar 5 1 aQ sLt, sel nar 6 aQ 1 sLt]

/-- `[j]` under the mask into the big-endian bytes at argument `arg`, as many as argument `arg + 1`. -/
def store (arg j : Nat) : Prog isa := seqs [
  sel nar j aZero j sMask,
  .block ([.mov .ebx (.mem (PublicFn.argument arg)), .mov .ecx (.mem (PublicFn.argument (arg + 1)))] ++
    arrPtr nar .esi j .edx ++ [.alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)]),
  reverseBytes]

def stores : Prog isa := seqs [store 0 5, store 2 6, .block [.mov .eax (.mem (sc sMask))]]

def factors : Prog isa := seqs [gcdSet, gcd nar, divSet, div nar aQ aRm aDv aDt, order]

def fin : Prog isa := seqs [finY, factors, stores]

/-! ## Fused exponentiation and root search -/

/-- Boolean header operations, with zero or one in each input slot. -/
def flagNot (d a : Nat) : Prog isa := .block [
  .mov .eax (.mem (sc a)), .alu .xor .eax (.imm 1), .store (sc d) .eax]

def flagBin (op : AluOp) (d a b : Nat) : Prog isa := .block [
  .mov .eax (.mem (sc a)), .alu op .eax (.mem (sc b)), .store (sc d) .eax]

/-- The square times the public candidate. Only the attempt index chooses
this loop's count; all arithmetic remains independent of private values. -/
def fusedSmallStep : Prog isa := .seq
  (seqs (FastAdd.addMod nar mXm mXm mX aN aZ mAcc))
  (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)])

def fusedSmall : Prog isa := seqs [copy nar mXm mX,
  .block [.mov .esi (.mem (sc sCand)), .alu .add .esi (.imm 1)],
  .loop fusedSmallStep .ne]

/-- Candidate setup without changing the exponent stream. -/
def fusedSetG : Prog isa := .seq (copy nar mG aZ) (.block (
  [.mov .ecx (.mem (sc sCand)), .alu .add .ecx (.imm 2)] ++
    arrPtr nar .eax mG .edx ++ [.store (at_ .eax 0) .ecx]))

/-- A bounded multiplication for later candidates: seven bits suffice for
all candidates through 101. Slots 37..40 are dead until factor extraction. -/
def fusedSmall7 : Prog isa := seqs [fusedSetG,
  copy nar mY mX, copy nar mXm aZ, .block [.mov .esi (.imm 7)],
  mulMod nar aZ mG mY mXm aN aW]

def fusedMultiply : Prog isa := .seq
  (.block [.mov .eax (.mem (sc sCand)), .alu .sub .eax (.imm 14)])
  (.iteCold .ae fusedSmall7 fusedSmall)

def fusedBitHead (k : Nat) : List Instr := [.mov .eax (.mem (sc sWin))] ++
  (if k = 0 then [] else [.shift .shr .eax k]) ++
  [.alu .and .eax (.imm 1), .store (sc sBit) .eax]

/-- Save a root only on a zero bit before the current chain has stopped;
a set bit discards the old chain's flags. -/
def fusedHit : Prog isa := seqs [
  flagNot sLive sDone, flagBin .and sLive sLive sE1,
  flagNot sMask sBit, flagBin .and sLive sLive sMask,
  flagBin .or sOk sOk sLive, flagBin .and sOk sOk sMask,
  flagBin .or sDone sDone sE1, flagBin .or sDone sDone sE2,
  flagBin .and sDone sDone sMask]

def fusedTail : Prog isa := seqs [flagBin .or sE1 sE1 sE2,
  flagBin .and sE1 sE1 sBit, flagBin .or sDone sDone sE1]

def fusedBit (k : Nat) : Prog isa := seqs [
  .block (fusedBitHead k), mmul mX mY mY, eqAt sE1 mX aO, eqAt sE2 mX aNg,
  fusedHit, sel nar 0 0 mY sLive, fusedMultiply, sel nar mY mX mXm sBit,
  eqAt sE1 mY aO, eqAt sE2 mY aNg, fusedTail]

def fusedBits : Prog isa := seqs [fusedBit 3, fusedBit 2, fusedBit 1, fusedBit 0]

def fusedWindow : Prog isa := seqs [.block windowTop, shiftUp, fusedBits, .block cntNext]

def fusedInit : Prog isa := .seq (copy nar 0 aZ) (.block [
  .mov .eax (.imm 1), .store (sc sDone) .eax,
  .mov .eax (.imm 0), .store (sc sOk) .eax, .store (sc sWin) .eax])

def fusedFinish : Prog isa := .seq (copy nar mY 0)
  (.block [.mov .eax (.imm 0), .store (sc sK) .eax])

def fusedCand : Prog isa := seqs [alignStart, .loop alignBody .ne,
  fusedInit, .block windowCount, .loop fusedWindow .ne, fusedFinish, .block candNext]

def fusedLoop : Prog isa := .seq
  (.block [.mov .eax (.imm 0), .store (sc sCand) .eax]) (.loop fusedCand .ne)

/-- Keep the full exponent; the fused pass needs no factor-of-two extraction. -/
def fusedPrepare : Prog isa := seqs [copy wid wR wM,
  .block [.mov .eax (.imm 0), .store (sc sTc) .eax, .store (sc sCnt) .eax]]

def fusedRest : Prog isa := seqs [fusedPrepare, mont, fusedLoop, fin]

def rest : Prog isa := seqs [halving, mont, candLoop, fin]

/-- The fixed seven-bit fallback costs more at small widths. The public
modulus length selects the existing schedule below 2048 bits. -/
def recoveryChoice : List Instr := [
  .mov .eax (.mem (PublicFn.argument 5)), .alu .sub .eax (.imm 256)]

def selectedRest : Prog isa := .seq (.block recoveryChoice) (.iteCold .b rest fusedRest)

def sized : Prog isa := .seq numbers (.ite .e selectedRest VG.Impl.Rsa.X86.Recover.failure)

def body : Prog isa := .seq
  (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 4)) (.seq (.block modulusCheck) (.ite .e sized VG.Impl.Rsa.X86.Recover.failure))

def code : Prog isa := .seq (.block entry) (.seq body (.block PublicFn.restore))

end FastAddProto

def main : IO Unit := do
  IO.FS.writeFile "/workspace/scratch/openssl/fastadd-generated.S" (SquareProto.printFn "proto_fastadd" FastAddProto.code)
