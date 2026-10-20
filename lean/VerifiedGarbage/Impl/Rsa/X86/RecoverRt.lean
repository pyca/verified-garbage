module

public import VerifiedGarbage.Impl.Rsa.X86.Recover
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
public import VerifiedGarbage.Impl.Mont.X86.MulRt

/-! # RSA prime recovery at a width read at run time (i686)

`Recover`'s schedule, arrays and header words without a copy per width: the
arrays are `KeyRt`'s, of the modulus's bytes `B` and two words more
(`narrow`, the numbers modulo `n`), or of `2 B + 24` bytes (`wide`, the
product `e d` and its halvings), two narrow arrays each; every Montgomery
multiplication calls `vg_rsa_mont_mul_at`, with the narrow arrays' offsets,
in its own range of the narrow arrays 16 to 19; and the candidate's table is
built by fourteen fixed steps. Only the public lengths choose loop counts,
and only whether to try candidates and when one succeeds choose branches, as
`Recover`'s do.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.RecoverRt
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.Keys (aM aNM aZero hdr seqs)
open VG.Impl.Rsa.X86.KeyRt (Lay Shape arrPtr bytesB sub3 copy sel half bitOf setOne clrLow eqS zeroArrays
  mulMod inverse div load restoreEdi)
open VG.Impl.Rsa.X86.Recover (sTc sCand sK sDone sOk sBit sLive sE1 sE2 sCnt sLt sInv sMask sWin sEq mAcc
  mBase mY mR2 mG mXm mX aN aOne aZ aO aNg aW aU aQ aRm aDv aDt nArr wZ wE wD wM wMod wT wH wU wR wRc
  entry skipTest cntBits cntNext sqInit sqMasks sqNext candNext)

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

def prodCount : List Instr := [.mov .esi (.mem (PublicFn.argument 7)),
  .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi)]

def prod : Prog isa := .seq (.block (setTop ++ prodCount)) (mulMod wid wZ wE wD wM wMod wT)

def skipBits : List Instr := bitOf wid sBit wM ++ clrLow wid wM

def numbers : Prog isa := seqs [loads, prod, .block skipBits, sub3 wid wT wZ wM, .block skipTest]

/-! ## The halvings of `e d - 1` -/

def halfInit : Prog isa := seqs [copy wid wR wM,
  .block ([.mov .eax (.imm 0), .store (sc sTc) .eax] ++ cntBits)]

def halfBit : List Instr := bitOf wid sBit wR ++ [
  .mov .eax (.mem (sc sBit)), .alu .xor .eax (.imm 1), .store (sc sBit) .eax,
  .mov .edx (.mem (sc sTc)), .alu .add .edx (.reg .eax), .store (sc sTc) .edx]

def halfBody : Prog isa := seqs [copy wid wU wR, copy wid wH wR,
  .block [.mov .ebx (.imm 0)], half wid wH, .block halfBit,
  sel wid wR wU wH sBit, .block cntNext]

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
  .loop (seqs (VG.Impl.Rsa.X86.KeyRt.addMod nar mR2 mR2 mR2 aN aZ mAcc ++
    [.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]])) .ne]

def mont : Prog isa := seqs [
  sub3 nar aZ aN aN, copy nar aOne aZ, .block (setOne nar aOne),
  copy nar mBase aN, .block setupInverse,
  setupR2, copy nar mXm aOne, mmul mXm mXm mR2,
  copy nar aO mXm, sub3 nar aNg aN aO]

/-! ## The candidates -/

def candSet : Prog isa := seqs [copy nar mG aZ,
  .block (arrPtr nar .ebx mG .edx ++ [.mov .eax (.mem (sc sCand)), .alu .add .eax (.imm 2),
    .store (at_ .ebx 0) .eax]),
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

/-- `c / 4` windows. -/
def windowCount : List Instr := [.mov .eax (.mem (PublicFn.argument 7)),
  .alu .add .eax (.mem (PublicFn.argument 9)), .alu .add .eax (.reg .eax), .store (sc sCnt) .eax]

/-- The table of the candidate's powers `0` to `15` (Montgomery form) in narrow arrays `0` to `15`. -/
def table : Prog isa := seqs ([copy nar 0 aO, copy nar 1 mG, copy nar mXm mG] ++
  (List.range 14).map fun i => .seq (mmul mXm mXm mG) (copy nar (i + 2) mXm))

/-- The exponent's top four bits, into `sWin`. -/
def windowTop : List Instr :=
  arrPtr wid .eax wRc .edx ++ [.alu .add .eax (.reg .edx), .alu .sub .eax (.imm 12), .mov .eax (.mem (at_ .eax 0)),
    .shift .shr .eax 28, .store (sc sWin) .eax]

/-- The window's entry into `mXm`, by a scan of entries `0` to `k`. -/
def scan : Nat → Prog isa
  | 0 => copy nar mXm 0
  | k + 1 => seqs [scan k, .block (VG.Impl.Rsa.X86.Recover.windowIs (k + 1)), sel nar mXm mXm (k + 1) sEq]

def square : Prog isa := mmul mY mY mY

def windowBody : Prog isa := seqs [square, square, square, square,
  .block windowTop, shiftUp, scan 15, mmul mY mY mXm, .block cntNext]

def eqAt (d a b : Nat) : Prog isa := eqS nar d a b aW

def sqBody : Prog isa := seqs [mmul mX mY mY,
  eqAt sE1 mX aO, eqAt sE2 mX aNg, .block sqMasks,
  copy nar aU mY, sel nar mY aU mX sLive, .block sqNext]

def candExp : Prog isa := seqs [alignStart, .loop alignBody .ne,
  mmul mG mG mR2, table, .block windowCount, .loop windowBody .ne]

def candSquare : Prog isa := seqs [eqAt sE1 mY aO, eqAt sE2 mY aNg,
  .block sqInit, .loop sqBody .ne]

def candBody : Prog isa := seqs [candExp, candSquare, .block candNext]

def candLoop : Prog isa := .seq
  (.block [.mov .eax (.imm 0), .store (sc sCand) .eax]) (.loop candBody .ne)

/-! ## The factors -/

def finY : Prog isa := seqs [
  .block [.mov .eax (.mem (sc sOk)), .store (sc sMask) .eax],
  copy nar mXm aOne, mmul mY mY mXm]

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

def factors : Prog isa := seqs [gcdSet, inverse nar, divSet, div nar aQ aRm aDv aDt, order]

def fin : Prog isa := seqs [finY, factors, stores]

def rest : Prog isa := seqs [halving, mont, candLoop, fin]

def sized : Prog isa := .seq numbers (.ite .e rest VG.Impl.Rsa.X86.Recover.failure)

def body : Prog isa := .seq
  (.block (CrtValues.inputArgs 4)) (.seq (.block modulusCheck) (.ite .e sized VG.Impl.Rsa.X86.Recover.failure))

def code : Prog isa := .seq (.block entry) (.seq body (.block PublicFn.restore))

end VG.Impl.Rsa.X86.RecoverRt
