module

public import VerifiedGarbage.Impl.Rsa.X86.MulMod
public import VerifiedGarbage.Impl.Rsa.X86.CrtValues
public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Impl.Mont.X86.Window

/-! # RSA prime recovery on i686

Public lengths select fixed workspace offsets. The only key-dependent
branches decide whether to try candidates and when a candidate succeeds,
as allowed by the existing recovery contract.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.Recover
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Rsa.X86.Keys
open VG.Impl.Bignum.X86

def sTc : Nat := 20
def sCand : Nat := 24
def sK : Nat := 28
def sDone : Nat := 32
def sOk : Nat := 36
def sBit : Nat := 40
def sLive : Nat := 44
def sE1 : Nat := 48
def sE2 : Nat := 52
def sCnt : Nat := 56
def sLt : Nat := 60
def sInv : Nat := 64
def sMask : Nat := 132
/-- The current window of the exponent, and whether it names a table entry. -/
def sWin : Nat := 68
def sEq : Nat := 72

def mAcc : Nat := 16
def mBase : Nat := 20
def mY : Nat := 21
def mTmp : Nat := 22
def mR2 : Nat := 24
def mG : Nat := 25
def mXm : Nat := 26
def mX : Nat := 27
def aN : Nat := 32
def aOne : Nat := 33
def aZ : Nat := 34
def aO : Nat := 35
def aNg : Nat := 36
def aW : Nat := 37
def aU : Nat := 38
def aQ : Nat := 40
def aRm : Nat := 41
def aDv : Nat := 42
def aDt : Nat := 43
def nArr : Nat := 44

def wZ : Nat := 0
def wE : Nat := 1
def wD : Nat := 2
def wM : Nat := 3
def wMod : Nat := 4
def wT : Nat := 5
def wH : Nat := 5
def wU : Nat := 6
def wR : Nat := 14
def wRc : Nat := 15

def width (n : Nat) : Nat := 2 * n + 2
def wide (n : Nat) : Nat := 2 * width n + 2

def entry : List Instr := [.mov .eax (.mem (PublicFn.argument 10))] ++
  PublicFn.save ++ [.mov .edi (.reg .eax)]

def failure : Prog isa := seqs [CrtValues.clear 0, CrtValues.clear 2,
  .block [.mov .eax (.imm 0)]]

/-- Import into the full array, including its two carry words. -/
def load (n arg j : Nat) : Prog isa := .seq (.block (CrtValues.inputArgs arg))
  (loadBE (n + 2) (slot (width n) j))

def loads (n : Nat) : Prog isa := seqs [
  Dynamic.zerosW hdr (nArr * (width n + 2)),
  load n 4 aN, load n 6 (2 * wE), load n 8 (2 * wD)]

def setTop (w j : Nat) : List Instr := [
  .mov .eax (.imm 0x80000000), .store (sc (slot w j + 4 * (w - 1))) .eax]

def prodCount : List Instr := [.mov .esi (.mem (PublicFn.argument 7)),
  .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi)]

def prodSet (n : Nat) : List Instr := setTop (wide n) wMod ++ prodCount

def prod (n : Nat) : Prog isa := .seq (.block (prodSet n))
  (mulMod (wide n) wZ wE wD wM wMod wT)

def skipBits (n : Nat) : List Instr := bitOf (wide n) sBit wM ++ clrLow (wide n) wM

def skipTest : List Instr := [.mov .eax (.mem (sc sBit)), .alu .and .eax (.reg .ebx),
  .alu .cmp .eax (.imm 1)]

def numbers (n : Nat) : Prog isa := seqs [loads n, prod n, .block (skipBits n),
  sub3 (wide n) wT wZ wM, .block skipTest]

def cntBits : List Instr := [.mov .eax (.mem (PublicFn.argument 7)),
  .alu .add .eax (.mem (PublicFn.argument 9)), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .store (sc sCnt) .eax]

def halfInit (n : Nat) : Prog isa := seqs [copy (wide n) wR wM,
  .block ([.mov .eax (.imm 0), .store (sc sTc) .eax] ++ cntBits)]

def halfBit (n : Nat) : List Instr := bitOf (wide n) sBit wR ++ [
  .mov .eax (.mem (sc sBit)), .alu .xor .eax (.imm 1), .store (sc sBit) .eax,
  .mov .edx (.mem (sc sTc)), .alu .add .edx (.reg .eax), .store (sc sTc) .edx]

def cntNext : List Instr := [.mov .eax (.mem (sc sCnt)), .alu .sub .eax (.imm 1),
  .store (sc sCnt) .eax]

def halfBody (n : Nat) : Prog isa := seqs [copy (wide n) wU wR, copy (wide n) wH wR,
  .block [.mov .ebx (.imm 0)], half (wide n) wH, .block (halfBit n),
  sel (wide n) wR wU wH sBit, .block cntNext]

def halving (n : Nat) : Prog isa := .seq (halfInit n) (.loop (halfBody n) .ne)

def montMod (n : Nat) : Mod := { n, mo := slot (width n) mBase, tmp := slot (width n) mTmp, minv := 0 }

def clrTop (n j : Nat) : Prog isa :=
  Dynamic.zerosW (slot (width n) j + 8 * n) 2

def mmul (n o a b : Nat) : Prog isa := .seq
  (Dynamic.mul (montMod n) sInv (slot (width n) mAcc)
    (slot (width n) o) (slot (width n) a) (slot (width n) b)) (clrTop n o)

def setupR2 (n : Nat) : Prog isa := .seq
  (Dynamic.powerTwo (montMod n) (slot (width n) mAcc) (slot (width n) mR2) (128 * n))
  (clrTop n mR2)

def mont (n : Nat) : Prog isa := seqs [
  sub3 (width n) aZ aN aN, copy (width n) aOne aZ, .block (setOne (width n) aOne),
  copy (width n) mBase aN, .block (Dynamic.setupInverse (slot (width n) mBase) sInv),
  setupR2 n, copy (width n) mXm aOne, mmul n mXm mXm mR2,
  copy (width n) aO mXm, sub3 (width n) aNg aN aO]

def candSet (n : Nat) : Prog isa := seqs [copy (width n) mG aZ,
  .block [.mov .eax (.mem (sc sCand)), .alu .add .eax (.imm 2),
    .store (sc (slot (width n) mG)) .eax],
  copy (width n) mY aO, copy (wide n) wRc wR]

/-! The candidate's power by fixed 4-bit windows of the exponent `r`, from its
top: `r < 2 ^ c` for the public bit count `c = 8 (e_len + d_len)`, so `r`
is first shifted up by the public `32 W - c` bits (`W` its words), four at a
time, to put its top window at the top of its words. The table of the
candidate's powers `0` to `15` takes slots `0` to `15`, whose numbers are
dead during the candidates. -/

/-- `32 W - c`, in four-bit shifts. -/
def alignCount (n : Nat) : List Instr := [.mov .eax (.mem (PublicFn.argument 7)),
  .alu .add .eax (.mem (PublicFn.argument 9)), .alu .add .eax (.reg .eax),
  .mov .edx (.imm (BitVec.ofNat 32 (8 * wide n))), .alu .sub .edx (.reg .eax), .store (sc sCnt) .edx]

def alignBody (n : Nat) : Prog isa :=
  .seq (Dynamic.shiftUp (wide n) (slot (wide n) wRc)) (.block cntNext)

/-- The candidate, and the alignment's count. -/
def alignStart (n : Nat) : Prog isa := .seq (candSet n) (.block (alignCount n))

/-- `c / 4` windows. -/
def windowCount : List Instr := [.mov .eax (.mem (PublicFn.argument 7)),
  .alu .add .eax (.mem (PublicFn.argument 9)), .alu .add .eax (.reg .eax), .store (sc sCnt) .eax]

/-- The next entry: the one below (`mXm`) times the candidate, into `mXm` and
the array at `esi`; until `esi` reaches array 16. -/
def tableStep (n : Nat) : Prog isa := seqs [mmul n mXm mXm mG,
  Dynamic.copyOut (width n) (slot (width n) mXm),
  .block [.alu .add .esi (.imm 8), .mov .edx (.reg .edi),
    .alu .add .edx (.imm (BitVec.ofNat 32 (slot (width n) 16))), .alu .cmp .esi (.reg .edx)]]

def table (n : Nat) : Prog isa := seqs [copy (width n) 0 aO, copy (width n) 1 mG,
  copy (width n) mXm mG,
  .block [.mov .esi (.reg .edi), .alu .add .esi (.imm (BitVec.ofNat 32 (slot (width n) 2)))],
  .loop (tableStep n) .ne]

/-- The exponent's top four bits, into `sWin`. -/
def windowTop (n : Nat) : List Instr :=
  [.mov .eax (.mem (sc (slot (wide n) wRc + 4 * (wide n - 1)))), .shift .shr .eax 28,
    .store (sc sWin) .eax]

/-- `sEq` is 1 exactly when the window is `j` (below 16). -/
def windowIs (j : Nat) : List Instr := [.mov .eax (.mem (sc sWin)),
  .alu .xor .eax (.imm (BitVec.ofNat 32 j)), .alu .sub .eax (.imm 1), .shift .shr .eax 31,
  .store (sc sEq) .eax]

/-- The window's entry into `mXm`, by a scan of entries `0` to `k`. -/
def scan (n : Nat) : Nat → Prog isa
  | 0 => copy (width n) mXm 0
  | k + 1 => seqs [scan n k, .block (windowIs (k + 1)), sel (width n) mXm mXm (k + 1) sEq]

def square (n : Nat) : Prog isa := mmul n mY mY mY

def windowBody (n : Nat) : Prog isa := seqs [square n, square n, square n, square n,
  .block (windowTop n), Dynamic.shiftUp (wide n) (slot (wide n) wRc), scan n 15,
  mmul n mY mY mXm, .block cntNext]

def eqAt (n d a b : Nat) : Prog isa := eqS (width n) d a b aW

def sqInit : List Instr := [.mov .eax (.mem (sc sE1)), .alu .or .eax (.mem (sc sE2)),
  .store (sc sDone) .eax, .mov .eax (.imm 0), .store (sc sOk) .eax,
  .store (sc sK) .eax] ++ cntBits

/-- EAX=k+1=t or x=-1; EDX=x=1; EBX=live; ECX=done; EBP=temporary. -/
def sqMasks : List Instr := [
  .mov .eax (.mem (sc sK)), .mov .edx (.mem (sc sTc)),
  .mov .ebx (.reg .eax), .alu .sub .ebx (.reg .edx), .shift .shr .ebx 31,
  .mov .ecx (.mem (sc sDone)), .mov .ebp (.reg .ecx), .alu .xor .ebp (.imm 1),
  .alu .and .ebx (.reg .ebp), .alu .add .eax (.imm 1), .alu .xor .eax (.reg .edx),
  .alu .sub .eax (.imm 1), .shift .shr .eax 31, .alu .or .eax (.mem (sc sE2)),
  .mov .edx (.mem (sc sE1)), .mov .ebp (.reg .ebx), .alu .and .ebp (.reg .edx),
  .alu .or .ebp (.mem (sc sOk)), .store (sc sOk) .ebp,
  .mov .ebp (.reg .edx), .alu .or .ebp (.reg .eax), .alu .and .ebp (.reg .ebx),
  .alu .or .ecx (.reg .ebp), .store (sc sDone) .ecx,
  .alu .xor .ebp (.imm 1), .alu .and .ebp (.reg .ebx), .store (sc sLive) .ebp]

def sqNext : List Instr := [.mov .eax (.mem (sc sK)), .alu .add .eax (.imm 1),
  .store (sc sK) .eax] ++ cntNext

def sqBody (n : Nat) : Prog isa := seqs [mmul n mX mY mY,
  eqAt n sE1 mX aO, eqAt n sE2 mX aNg, .block sqMasks,
  copy (width n) aU mY, sel (width n) mY aU mX sLive, .block sqNext]

def candNext : List Instr := [.mov .eax (.mem (sc sCand)), .alu .add .eax (.imm 1),
  .store (sc sCand) .eax, .alu .sub .eax (.imm 100), .shift .shr .eax 31,
  .mov .edx (.mem (sc sOk)), .alu .xor .edx (.imm 1), .alu .and .eax (.reg .edx),
  .alu .cmp .eax (.imm 0)]

def candExp (n : Nat) : Prog isa := seqs [alignStart n, .loop (alignBody n) .ne,
  mmul n mG mG mR2, table n, .block windowCount, .loop (windowBody n) .ne]

def candSquare (n : Nat) : Prog isa := seqs [eqAt n sE1 mY aO, eqAt n sE2 mY aNg,
  .block sqInit, .loop (sqBody n) .ne]

def candBody (n : Nat) : Prog isa := seqs [candExp n, candSquare n, .block candNext]

def candLoop (n : Nat) : Prog isa := .seq
  (.block [.mov .eax (.imm 0), .store (sc sCand) .eax]) (.loop (candBody n) .ne)

def finY (n : Nat) : Prog isa := seqs [
  .block [.mov .eax (.mem (sc sOk)), .store (sc sMask) .eax],
  copy (width n) mXm aOne, mmul n mY mY mXm]

def gcdSet (n : Nat) : Prog isa := seqs [sub3 (width n) 0 mY aOne,
  copy (width n) 1 aN, copy (width n) aM aN, copy (width n) 2 aZ,
  .block (setOne (width n) 2), copy (width n) 3 aZ, copy (width n) aZero aZ,
  sub3 (width n) aNM aZero aM]

def divSet (n : Nat) : Prog isa := seqs [copy (width n) aQ aN,
  copy (width n) aDv 1, .block [.mov .eax (.imm 0),
    .store (sc (slot (width n) aDv + 4 * width n)) .eax]]

def order (n : Nat) : Prog isa := seqs [sub3 (width n) aW 1 aQ,
  .block [.store (sc sLt) .ebx], sel (width n) 5 1 aQ sLt, sel (width n) 6 aQ 1 sLt]

def stores (n : Nat) : Prog isa := seqs [CrtValues.store (n + 1) 0 5,
  CrtValues.store (n + 1) 2 6, .block [.mov .eax (.mem (sc sMask))]]

def factors (n : Nat) : Prog isa := seqs [gcdSet n, inverse (width n), divSet n,
  Div.code (width n) (slot (width n) aQ) (slot (width n) aRm)
    (slot (width n) aDv) (slot (width n) aDt), order n]

def fin (n : Nat) : Prog isa := seqs [finY n, factors n, stores n]

def rest (n : Nat) : Prog isa := seqs [halving n, mont n, candLoop n, fin n]
def sized (n : Nat) : Prog isa := .seq (numbers n) (.ite .e (rest n) failure)

def dispatch : List Nat → Prog isa
  | [] => failure
  | n :: ns => .seq (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 n))])
      (.ite .e (sized n) (dispatch ns))

def valid : Prog isa := .seq (.block [.mov .eax (.mem (PublicFn.argument 5)),
  .alu .add .eax (.imm 7), .shift .shr .eax 3]) (dispatch PublicFn.widths)

def body : Prog isa := .seq
  (.block (CrtValues.inputArgs 4)) (.seq (.block modulusCheck) (.ite .e valid failure))

def code : Prog isa := .seq (.block entry) (.seq body (.block PublicFn.restore))
end VG.Impl.Rsa.X86.Recover
