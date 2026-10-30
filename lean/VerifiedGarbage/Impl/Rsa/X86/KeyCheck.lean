module

public import VerifiedGarbage.Impl.Rsa.X86.KeyWs
public import VerifiedGarbage.Impl.Rsa.X86.CrtValues

/-! # Validation of RSA private-key components on i686: the layout

The header words, arrays, inputs and entry `KeyCheckRt`'s checks use.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.KeyCheck
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.Keys

def sF : Nat := 116
def sMask : Nat := 120

/-! ## The arrays -/

def aZ : Nat := 0
def aOne : Nat := 1
def aN : Nat := 2
def aE : Nat := 3
def aP : Nat := 4
def aQ : Nat := 5
def aDP : Nat := 6
def aDQ : Nat := 7
def aQI : Nat := 8
def aD : Nat := 9
def aM1 : Nat := 10
def aM2 : Nat := 11
/-- The division's quotient, remainder, divisor and temporary. -/
def aVQ : Nat := 12
def aVR : Nat := 13
def aVD : Nat := 14
def aVT : Nat := 15
/-- `mulMod`'s multiplier, multiplicand, accumulator, and its four
temporaries 19–22. -/
def aY : Nat := 16
def aX : Nat := 17
def aA : Nat := 18
def aT : Nat := 19
/-- The temporary of the comparisons. -/
def aW : Nat := 23
/-- The number of arrays. -/
def nArr : Nat := 24

def acc : List Instr := andS sMask sMask sF

/-- The cdecl pointer/length pair index for each input array. -/
def inputs (full : Bool) : List (Nat × Nat) :=
  [(0, aN), (1, aE)] ++ (if full then [(2, aD)] else []) ++
  [(if full then 3 else 2, aP), (if full then 4 else 3, aQ),
   (if full then 5 else 4, aDP), (if full then 6 else 5, aDQ),
   (if full then 7 else 6, aQI)]

def scratchArg (full : Bool) : Nat := if full then 16 else 14

/-- The cdecl argument holding `q`'s length in bytes. -/
def qLenArg (full : Bool) : Nat := if full then 9 else 7

def entry (full : Bool) : List Instr :=
  [.mov .eax (.mem (VG.Impl.Bignum.X86.PublicFn.argument (scratchArg full)))] ++
  VG.Impl.Bignum.X86.PublicFn.save ++ [.mov .edi (.reg .eax)]

def failure : Prog isa := .block [.mov .eax (.imm 0)]

end VG.Impl.Rsa.X86.KeyCheck
