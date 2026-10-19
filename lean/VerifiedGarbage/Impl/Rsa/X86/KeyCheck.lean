module

public import VerifiedGarbage.Impl.Rsa.X86.MulMod
public import VerifiedGarbage.Impl.Rsa.X86.CrtValues

/-! # Fixed-schedule validation of RSA private-key components on i686

Checks the factor product, reduced exponents and inverse, then optionally
the full private exponent. Every check contributes to a mask; secret
values do not select branches or addresses.
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

def ltA (w a b : Nat) : List (Prog isa) :=
  [sub3 w aW a b, .block [.store (sc sF) .ebx], .block acc]

def eqA (w a b : Nat) : List (Prog isa) := [eqS w sF a b aW, .block acc]

def divSet (w a d : Nat) : List (Prog isa) := [copy w aVQ a, copy w aVD d]

def division (w : Nat) : Prog isa := Div.code w (slot w aVQ) (slot w aVR) (slot w aVD) (slot w aVT)

def mulA (w y x m : Nat) (cnt : List Instr) : List (Prog isa) :=
  [copy w aY y, copy w aX x, copy w aA aZ, .block cnt, mulMod w aZ aY aX aA m aT]

def cnt33 : List Instr := [.mov .esi (.imm 33)]
def cntW (w : Nat) : List Instr := [.mov .esi (.imm (BitVec.ofNat 32 (32 * w)))]

def start (w : Nat) : Prog isa := seqs ([.block (setOne w aOne), .block (bitOf w sMask aP)] ++ divSet w aN aP)

def crtChecks (w : Nat) : Prog isa := seqs (eqA w aVQ aQ ++ eqA w aVR aZ ++
  [copy w aM1 aP, .block (clrLow w aM1), copy w aM2 aQ, .block (clrLow w aM2)] ++
  ltA w aDP aM1 ++ mulA w aE aDP aM1 cnt33 ++ eqA w aA aOne ++
  ltA w aDQ aM2 ++ mulA w aE aDQ aM2 cnt33 ++ eqA w aA aOne ++
  ltA w aQI aP ++ mulA w aQ aQI aP (cntW w) ++ eqA w aA aOne)

def crtBody (w : Nat) : Prog isa := seqs [start w, division w, crtChecks w]

def dChecks1 (w : Nat) : Prog isa := seqs (ltA w aD aN ++ divSet w aD aM1)
def dChecks2 (w : Nat) : Prog isa := seqs (eqA w aVR aDP ++ divSet w aD aM2)
def dChecks3 (w : Nat) : Prog isa := seqs (eqA w aVR aDQ)

def keyBody (w : Nat) : Prog isa := seqs [crtBody w, dChecks1 w, division w,
  dChecks2 w, division w, dChecks3 w]

/-- The cdecl pointer/length pair index for each input array. -/
def inputs (full : Bool) : List (Nat × Nat) :=
  [(0, aN), (1, aE)] ++ (if full then [(2, aD)] else []) ++
  [(if full then 3 else 2, aP), (if full then 4 else 3, aQ),
   (if full then 5 else 4, aDP), (if full then 6 else 5, aDQ),
   (if full then 7 else 6, aQI)]

def scratchArg (full : Bool) : Nat := if full then 16 else 14

def entry (full : Bool) : List Instr :=
  [.mov .eax (.mem (VG.Impl.Bignum.X86.PublicFn.argument (scratchArg full)))] ++
  VG.Impl.Bignum.X86.PublicFn.save ++ [.mov .edi (.reg .eax)]

def loadInputs (n : Nat) : List (Nat × Nat) → Prog isa
  | [] => .block []
  | (i, j) :: rest => .seq (CrtValues.load n (2 * i) j) (loadInputs n rest)

def loads (full : Bool) (n : Nat) : Prog isa :=
  .seq (Dynamic.zerosW hdr (nArr * (2 * n + 2)))
    (loadInputs n (inputs full))

def sized (full : Bool) (n : Nat) : Prog isa := seqs [loads full n,
  (if full then keyBody (2 * n) else crtBody (2 * n)), .block [.mov .eax (.mem (sc sMask))]]

def failure : Prog isa := .block [.mov .eax (.imm 0)]

def dispatch (full : Bool) : List Nat → Prog isa
  | [] => failure
  | n :: rest => .seq (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 n))])
      (.ite .e (sized full n) (dispatch full rest))

def valid (full : Bool) : Prog isa :=
  .seq (.block [.mov .eax (.mem (VG.Impl.Bignum.X86.PublicFn.argument 1)),
    .alu .add .eax (.imm 7), .shift .shr .eax 3])
    (dispatch full VG.Impl.Bignum.X86.PublicFn.widths)

def checkExponent (full : Bool) : Prog isa :=
  .seq (.seq (.block (CrtValues.inputArgs 2)) VG.Impl.Bignum.X86.exponentCheck)
    (.seq (.block [.alu .cmp .eax (.imm 0)]) (.ite .e failure (valid full)))

def body (full : Bool) : Prog isa :=
  .seq (.seq (.block (CrtValues.inputArgs 0)) (.block VG.Impl.Bignum.X86.modulusCheck))
    (.ite .e (checkExponent full) failure)

def code (full : Bool) : Prog isa :=
  .seq (.block (entry full)) (.seq (body full) (.block VG.Impl.Bignum.X86.PublicFn.restore))

end VG.Impl.Rsa.X86.KeyCheck
