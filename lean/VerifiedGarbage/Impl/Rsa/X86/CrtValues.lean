module

public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn

/-! # CRT parameter calculation on i686: its layout and pieces

The working space's header words and arrays, the entry, an input's load and
an output's store at a fixed width, and the failure that clears the outputs,
which `CrtValuesRt` and the key checks and prime recovery share.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.CrtValues
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.Keys
open VG.Impl.Bignum.X86

def sPodd : Nat := 116
def sE1 : Nat := 120
def sE2 : Nat := 124
def sE3 : Nat := 128
def sMask : Nat := 132

def aOne : Nat := 15
def aQ : Nat := 16
def aP : Nat := 17
def aDQ : Nat := 18
def aDR : Nat := 19
def aDD : Nat := 20
def aDT : Nat := 21
def aDR2 : Nat := 22
def aDR3 : Nat := 23
def aD : Nat := 24
def nArr : Nat := 25

def entry : List Instr :=
  [.mov .eax (.mem (PublicFn.argument 14))] ++ PublicFn.save ++ [.mov .edi (.reg .eax)]

def inputArgs (i : Nat) : List Instr :=
  [.mov .esi (.mem (PublicFn.argument i)), .mov .ecx (.mem (PublicFn.argument (i + 1)))]

def load (n arg j : Nat) : Prog isa :=
  .seq (.block (inputArgs arg)) (loadBE n (slot (2 * n) j))

def store (n arg j : Nat) : Prog isa := seqs [
  sel (2 * n) j aZero j sMask,
  .block [.mov .ebx (.mem (PublicFn.argument arg)), .mov .ecx (.mem (PublicFn.argument (arg + 1)))],
  storeBE (slot (2 * n) j)]

def clear (arg : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.mem (PublicFn.argument arg)),
    .mov .ecx (.mem (PublicFn.argument (arg + 1))), .mov .eax (.imm 0)])
    (.loop (.block PublicFn.clearStep) .ne)

def failure : Prog isa := seqs [clear 0, clear 2, clear 4]

end VG.Impl.Rsa.X86.CrtValues
