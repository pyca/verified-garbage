module

public import VerifiedGarbage.Impl.Rsa.X86.Recover
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Impl.Rsa.X86.GcdBatchRt
import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
public import VerifiedGarbage.Impl.Mont.X86.Sse2
public import VerifiedGarbage.Impl.Bignum.X86.CrtRt
public import VerifiedGarbage.Impl.Rsa.X86.CrtValues

/-! # RSA prime recovery at a width read at run time (i686)

`Recover`'s schedule, arrays and header words without a copy per width: the
arrays are `KeyRt`'s, of the modulus's bytes `B` and two words more
(`narrow`, the numbers modulo `n`), or of `2 B + 24` bytes (`wide`, the
product `e d` and its halvings), two narrow arrays each; every Montgomery
multiplication calls `vg_rsa_mont_mul_at`, with the narrow arrays' offsets,
in its own range of the narrow arrays 16 to 19; and small moduli retain the four-bit window table. At 2048 bits and
above, one fixed-width binary pass fuses exponentiation with root search.
Public lengths and candidate indices choose loop counts; the search ends
after the declared number of attempts. Private values select no branch.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.RecoverRt
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.Keys (aM aNM aZero hdr seqs)
open VG.Impl.Rsa.X86.KeyRt (Lay Shape arrPtr bytesB sub3 copy sel half bitOf setOne clrLow eqSFast zeroArrays
  mulMod gcd div load restoreEdi)
open VG.Impl.Rsa.X86.Recover (sTc sCand sK sDone sOk sBit sLive sE1 sE2 sCnt sLt sInv sMask sWin sEq mAcc
  mBase mY mR2 mG mXm mX aN aOne aZ aO aNg aW aQ aRm aDv aDt nArr wZ wE wD wM wMod wT wH wR wRc
  entry skipTest cntBits cntNext sqInit sqMasks sqNext candNext prodCount windowCount)

/-- The modulus's length (argument 5) and the working space (argument 10), with `k` words pushed. -/
def lay (shape : Shape) (k : Nat := 0) : Lay := { len := 5 + k, ws := 10 + k, shape, doubling := true }

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
  .seq (.frame (.alloc 36) (.seq (.block (mulArgs o a b)) (.call "vg_rsa_mont_mul_at" Sse2.atBody)) (.free 36))
    (.block (clrTop o))

/-- `-n⁻¹ mod 2³²` from `[mBase]`'s low word. -/
def setupInverse : List Instr :=
  arrPtr nar .eax mBase .edx ++ [.mov .ebx (.mem (at_ .eax 0))] ++ Dynamic.inverse ++ [.store (sc sInv) .eax]

/-- `[mR2] = R² mod n`: one, doubled `16 B` times modulo `n` through the callee's range (`mAcc` to
`mAcc + 2`), with `[aZ]` zero. -/
def setupR2 : Prog isa := seqs [copy nar mR2 aOne,
  .block (bytesB nar .esi ++ [.alu .sub .esi (.imm 8), .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi),
    .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi)]),
  .loop (seqs (VG.Impl.Rsa.X86.KeyRt.addMod nar mR2 mR2 mR2 aN aZ mAcc ++
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

def factorTail : Prog isa := seqs [divSet, div nar aQ aRm aDv aDt, order]

def factors : Prog isa := seqs [gcdSet, GcdBatchRt.body wid, factorTail]

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
  (seqs (VG.Impl.Rsa.X86.KeyRt.addMod nar mXm mXm mX aN aZ mAcc))
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

def fusedRest : Prog isa := seqs [fusedPrepare, mont, fusedLoop]

def rest : Prog isa := seqs [halving, mont, candLoop]

/-- The fixed seven-bit fallback costs more at small widths. The public
modulus length selects the existing schedule below 2048 bits. -/
def recoveryChoice : List Instr := [
  .mov .eax (.mem (PublicFn.argument 5)), .alu .sub .eax (.imm 256)]

/-- Either schedule's search, then the factors from its result: `fin` is shared. -/
def selectedRest : Prog isa := .seq (.block recoveryChoice) (.seq (.iteCold .b rest fusedRest) fin)

def sized : Prog isa := .seq numbers (.ite .e selectedRest VG.Impl.Rsa.X86.Recover.failure)

def body : Prog isa := .seq
  (.block (CrtValues.inputArgs 4)) (.seq (.block modulusCheck) (.ite .e sized VG.Impl.Rsa.X86.Recover.failure))

def code : Prog isa := .seq (.block entry) (.seq body (.block PublicFn.restore))

end VG.Impl.Rsa.X86.RecoverRt
