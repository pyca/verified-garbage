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

def prodCount : List Instr := [.mov .esi (.mem (PublicFn.argument 7)),
  .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi)]

def skipTest : List Instr := [.mov .eax (.mem (sc sBit)), .alu .and .eax (.reg .ebx),
  .alu .cmp .eax (.imm 1)]

def cntBits : List Instr := [.mov .eax (.mem (PublicFn.argument 7)),
  .alu .add .eax (.mem (PublicFn.argument 9)), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .store (sc sCnt) .eax]

def cntNext : List Instr := [.mov .eax (.mem (sc sCnt)), .alu .sub .eax (.imm 1),
  .store (sc sCnt) .eax]

/-! The candidate's power by fixed 4-bit windows of the exponent `r`, from its
top: `r < 2 ^ c` for the public bit count `c = 8 (e_len + d_len)`, so `r`
is first shifted up by the public `32 W - c` bits (`W` its words), four at a
time, to put its top window at the top of its words. The table of the
candidate's powers `0` to `15` takes slots `0` to `15`, whose numbers are
dead during the candidates. -/

/-- `c / 4` windows. -/
def windowCount : List Instr := [.mov .eax (.mem (PublicFn.argument 7)),
  .alu .add .eax (.mem (PublicFn.argument 9)), .alu .add .eax (.reg .eax), .store (sc sCnt) .eax]

/-- `sEq` is 1 exactly when the window is `j` (below 16). -/
def windowIs (j : Nat) : List Instr := [.mov .eax (.mem (sc sWin)),
  .alu .xor .eax (.imm (BitVec.ofNat 32 j)), .alu .sub .eax (.imm 1), .shift .shr .eax 31,
  .store (sc sEq) .eax]

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

def candNext : List Instr := [.mov .eax (.mem (sc sCand)), .alu .add .eax (.imm 1),
  .store (sc sCand) .eax, .alu .sub .eax (.imm 100), .shift .shr .eax 31,
  .mov .edx (.mem (sc sOk)), .alu .xor .edx (.imm 1), .alu .and .eax (.reg .edx),
  .alu .cmp .eax (.imm 0)]

end VG.Impl.Rsa.X86.Recover
