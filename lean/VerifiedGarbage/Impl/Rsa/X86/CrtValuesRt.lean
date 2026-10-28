module

public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Impl.Rsa.X86.CrtValues

/-! # CRT parameter calculation at a width read at run time (i686)

`CrtValues`' computation without a copy per width: the arrays, header words
and schedule are `CrtValues`', every operation `KeyRt`'s, with the width from
the modulus's length `n_len` (argument 7) and the working space `scratch`
(argument 14).
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Rsa.X86.Keys VG.Impl.Rsa.X86.KeyRt
open VG.Impl.Rsa.X86.CrtValues (sPodd sE1 sE2 sE3 sMask aOne aQ aP aDQ aDR aDD aDT aDR2 aDR3 aD nArr
  entry inputArgs failure)

/-- `n_len` and `scratch`. -/
def lay : Lay := { len := 7, ws := 14, doubling := true }

def div (r : Nat) : Prog isa := KeyRt.div lay aDQ r aDD aDT

def invSetup : List (Prog isa) := [
  copy lay 0 aQ, copy lay aM aP, .block (orOne lay aM), copy lay 1 aM,
  .block (setOne lay 2 ++ setOne lay aOne), sub3 lay aNM aZero aM]

def inverseChoice : Prog isa := InvBatch.dispatch (inverse lay)

def checksPrefix : List (Prog isa) := [
  eqS lay sE1 aDQ aQ aT1,eqS lay sE2 aDR aZero aT1] ++ invSetup

def checksSuffix : List (Prog isa) := [eqS lay sE3 1 aOne aT1,
  .block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3),
  copy lay aDQ aD,copy lay aDD aP,.block (clrLow lay aDD)]

def checks : Prog isa := seqs (checksPrefix ++ inverseChoice::checksSuffix)

def firstDiv : Prog isa := seqs [
  copy lay aDD aP, .block (bitOf lay sPodd aP), div aDR]

def divQ : Prog isa := seqs [
  copy lay aDQ aD, copy lay aDD aQ, .block (clrLow lay aDD), div aDR3]

def core : Prog isa :=
  .seq firstDiv (.seq checks (.seq (div aDR2) divQ))

/-- Array `j` from the big-endian bytes at argument `arg`, as many as argument `arg + 1`. -/
def load (arg j : Nat) : Prog isa :=
  .seq (.block (inputArgs arg ++ arrPtr lay .ebx j .edx ++ [.alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)]))
    reverseBytes

def loads : Prog isa := seqs [
  zeroArrays lay nArr, load 6 aDQ, load 8 aP, load 10 aQ, load 12 aD]

/-- Array `j`, cleared unless the checks passed, to argument `arg`, as many bytes as argument `arg + 1`. -/
def store (arg j : Nat) : Prog isa := seqs [
  sel lay j aZero j sMask,
  .block ([.mov .ebx (.mem (PublicFn.argument arg)), .mov .ecx (.mem (PublicFn.argument (arg + 1)))] ++
    arrPtr lay .esi j .edx ++ [.alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)]),
  reverseBytes]

def stores : Prog isa := seqs [
  store 0 aDR2, store 2 aDR3, store 4 3,
  .block [.mov .eax (.mem (sc sMask))]]

def sized : Prog isa := seqs [loads, core, stores]

def body : Prog isa :=
  .seq (.block (inputArgs 6)) (.seq (.block modulusCheck) (.ite .e sized failure))

def code : Prog isa := .seq (.block entry) (.seq body (.block PublicFn.restore))

end VG.Impl.Rsa.X86.CrtValuesRt
