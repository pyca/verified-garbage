module

public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Impl.Rsa.X86.KeyCheck

/-! # Validation of RSA private-key components at a width read at run time (i686)

`KeyCheck`'s checks without a copy per width: the arrays, header words and
schedule are `KeyCheck`'s, every operation `KeyRt`'s, with the width from
the modulus's length `n_len` (argument 1) and the working space `scratch`
(argument 16 for the full key, 14 for the CRT key).
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.KeyCheckRt
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Rsa.X86.Keys VG.Impl.Rsa.X86.KeyRt
open VG.Impl.Rsa.X86.KeyCheck (sF sMask aZ aOne aN aE aP aQ aDP aDQ aQI aD aM1 aM2 aVQ aVR aVD aVT aY aX aA aT aW
  nArr acc cnt33 inputs scratchArg entry failure)

/-- `n_len` and `scratch`. -/
def lay (full : Bool) : Lay := { len := 1, ws := scratchArg full }

variable (full : Bool)

def ltA (a b : Nat) : List (Prog isa) :=
  [sub3 (lay full) aW a b, .block [.store (sc sF) .ebx], .block acc]

def eqA (a b : Nat) : List (Prog isa) := [eqS (lay full) sF a b aW, .block acc]

def divSet (a d : Nat) : List (Prog isa) := [copy (lay full) aVQ a, copy (lay full) aVD d]

def division : Prog isa := KeyRt.div (lay full) aVQ aVR aVD aVT

def mulA (y x m : Nat) (cnt : List Instr) : List (Prog isa) :=
  [copy (lay full) aY y, copy (lay full) aX x, copy (lay full) aA aZ, .block cnt,
    mulMod (lay full) aZ aY aX aA m aT]

def start : Prog isa :=
  seqs ([.block (setOne (lay full) aOne), .block (bitOf (lay full) sMask aP)] ++ divSet full aN aP)

def crtChecks : Prog isa := seqs (eqA full aVQ aQ ++ eqA full aVR aZ ++
  [copy (lay full) aM1 aP, .block (clrLow (lay full) aM1), copy (lay full) aM2 aQ, .block (clrLow (lay full) aM2)] ++
  ltA full aDP aM1 ++ mulA full aE aDP aM1 cnt33 ++ eqA full aA aOne ++
  ltA full aDQ aM2 ++ mulA full aE aDQ aM2 cnt33 ++ eqA full aA aOne ++
  ltA full aQI aP ++ mulA full aQ aQI aP (bits (lay full)) ++ eqA full aA aOne)

def crtBody : Prog isa := seqs [start full, division full, crtChecks full]

def dChecks1 : Prog isa := seqs (ltA full aD aN ++ divSet full aD aM1)
def dChecks2 : Prog isa := seqs (eqA full aVR aDP ++ divSet full aD aM2)
def dChecks3 : Prog isa := seqs (eqA full aVR aDQ)

def keyBody : Prog isa := seqs [crtBody full, dChecks1 full, division full,
  dChecks2 full, division full, dChecks3 full]

def loadInputs : List (Nat × Nat) → Prog isa
  | [] => .block []
  | (i, j) :: rest => .seq (load (lay full) (2 * i) j) (loadInputs rest)

def loads : Prog isa := .seq (zeroArrays (lay full) nArr) (loadInputs full (inputs full))

def sized : Prog isa := seqs [loads full,
  (if full then keyBody full else crtBody full), .block [.mov .eax (.mem (sc sMask))]]

def checkExponent : Prog isa :=
  .seq (.seq (.block (CrtValues.inputArgs 2)) exponentCheck)
    (.seq (.block [.alu .cmp .eax (.imm 0)]) (.ite .e failure (sized full)))

def body : Prog isa :=
  .seq (.seq (.block (CrtValues.inputArgs 0)) (.block modulusCheck))
    (.ite .e (checkExponent full) failure)

def code : Prog isa := .seq (.block (entry full)) (.seq (body full) (.block PublicFn.restore))

end VG.Impl.Rsa.X86.KeyCheckRt
