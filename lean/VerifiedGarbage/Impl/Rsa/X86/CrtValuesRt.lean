module

public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Impl.Rsa.X86.InvBatchRt
public import VerifiedGarbage.Impl.Rsa.X86.CrtValues
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Inverse
public import VerifiedGarbage.Impl.Rsa.X86.WordModRt

/-! # CRT parameter calculation at a width read at run time (i686)

`CrtValues`' computation without a copy per width: the arrays, header words
and schedule are `CrtValues`', every operation `KeyRt`'s, with the width from
the modulus's length `n_len` (argument 7) and the working space `scratch`
(argument 14). The general inverse, for lengths the batches do not take, is
a call of `vg_rsa_keygen_inverse`, which runs `KeyRt.inverse` on the same
arrays.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Rsa.X86.Keys VG.Impl.Rsa.X86.KeyRt
open VG.Impl.Rsa.X86.CrtValues (sPodd sE1 sE3 sMask aOne aQ aP aDQ aDR aDD aDT aDR2 aDR3 aD nArr
  entry inputArgs failure)

/-- `n_len` and `scratch`. -/
def lay : Lay := { len := 7, ws := 14, doubling := true }

def div (r : Nat) : Prog isa := KeyRt.div lay aDQ r aDD aDT

def invSetup : List (Prog isa) := [
  copy lay 0 aQ, copy lay aM aP, .block (orOne lay aM), copy lay 1 aM,
  .block (setOne lay 2 ++ setOne lay aOne), sub3 lay aNM aZero aM]

/-- The arguments of `vg_rsa_keygen_inverse` at the modulus's width: `eax` its length argument,
`ecx` the `35 + 15 ⌈len / 8⌉` words its header and fifteen numbers take. -/
def inverseArgs : List Instr :=
  [.mov .eax (.mem (argOp lay.len)), .mov .ecx (.reg .eax),
    .alu .add .ecx (.imm 7), .shift .shr .ecx 3, .mov .edx (.reg .ecx), .alu .add .ecx (.reg .ecx),
    .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
    .alu .sub .ecx (.reg .edx), .alu .add .ecx (.imm 35)]

/-- The call, with `edi` the working space. -/
def inverseCall : Prog isa :=
  .frame (.push [.eax, .ecx, .edi]) (.call "vg_rsa_keygen_inverse" VG.Impl.RsaKeyGen.X86.Inverse.code)
    (.pop .eax 3)

/-- A header word of the batches' window, which the general inverse leaves free. -/
def sOne : Nat := 16

/-- `[j]`'s low word plus twice the header word `sl`. -/
def addLowTwice (j sl : Nat) : List Instr :=
  arrPtr lay .eax j .edx ++ [.mov .ecx (.mem (at_ .eax 0)), .alu .add .ecx (.mem (sc sl)),
    .alu .add .ecx (.mem (sc sl)), .store (at_ .eax 0) .ecx]

/-- The modulus `m` made more than 1, as `vg_rsa_keygen_inverse` needs: 3 where it is 1 (a
`p` below 2, whose results the mask clears), else as it was; then `[1] = m` and
`[aNM] = 2^(32 w) - m` again. -/
def modulusAbove : List (Prog isa) := [
  eqSFast lay sOne aM 2, .block (addLowTwice aM sOne), copy lay 1 aM, sub3 lay aNM aZero aM]

/-- What the call needs: the modulus more than 1, and the arguments. -/
def callSetup : Prog isa := .seq (seqs modulusAbove) (.block inverseArgs)

/-- The general inverse, `KeyRt.inverse`, by a call of `vg_rsa_keygen_inverse` on the working space. -/
def fallback : Prog isa := .seq callSetup inverseCall

def inverseChoice : Prog isa := InvBatchRt.dispatch lay fallback

def checksPrefix : List (Prog isa) := [WordModRt.eqWide lay sE1 aDR2 aDQ] ++ invSetup

def checksSuffix : List (Prog isa) := [eqS lay sE3 1 aOne aT1,
  .block (andS sMask sPodd sE1 ++ andS sMask sMask sE3),
  copy lay aDQ aD,copy lay aDD aP,.block (clrLow lay aDD)]

def checks : Prog isa := seqs (checksPrefix ++ inverseChoice::checksSuffix)

/-- The header word holding the guard (`WordModRt.balanced`), which the word steps need. -/
def sG : Nat := 144

/-- The product `p q` (`2 w` words in `aDR2` and `aDR3`), compared with `n` (`aDQ`) by the checks. -/
def firstDiv : Prog isa := seqs [
  .block (bitOf lay sPodd aP ++ WordModRt.balanced lay 7 9 11 aDQ sG), WordModRt.mulWide lay aDR2 aP aQ]

/-- `d mod (p - 1)` into `aDR2` and `d mod (q - 1)` into `aDR3`, `rem` the remainder of
`[aDQ]` (`d`) by `[aDD]` into an array. -/
def rems (rem : Nat → Prog isa) : Prog isa := seqs [
  rem aDR2, copy lay aDQ aD, copy lay aDD aQ, .block (clrLow lay aDD), rem aDR3]

/-- The remainders by word steps (`aDD` of `p`'s length, argument 9; under the guard, `q`'s too). -/
def wordRems : Prog isa := rems fun r => WordModRt.wordMod lay 9 aDQ r aDD aDT

/-- The remainders by `KeyRt.div`. -/
def divRems : Prog isa := rems div

/-- The checks, then the remainders: by word steps under the guard (read once), else bit by bit. -/
def core : Prog isa :=
  .seq firstDiv (.seq checks (WordModRt.ifBalanced sG wordRems divRems))

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
