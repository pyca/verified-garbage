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
  nArr acc inputs scratchArg qLenArg entry failure)

/-- `n_len` and `scratch`. -/
def lay (full : Bool) : Lay := { len := 1, ws := scratchArg full, doubling := true }

variable (full : Bool)

def ltA (a b : Nat) : List (Prog isa) :=
  [sub3 (lay full) aW a b, .block [.store (sc sF) .ebx], .block acc]

def eqA (a b : Nat) : List (Prog isa) := [eqS (lay full) sF a b aW, .block acc]

def divSet (a d : Nat) : List (Prog isa) := [copy (lay full) aVQ a, copy (lay full) aVD d]

def division : Prog isa := KeyRt.div (lay full) aVQ aVR aVD aVT

/-! ## The three product checks, in one loop

`esi` holds the check's index `i` (3: `dP`, 2: `dQ`, 1: `qInv`) in its low half and, during the
product, its steps in its high half, so that one copy of the product serves the three. -/

/-- `esi`'s high half counts the steps of `mulModHi`. -/
def stepUnit : Nat := 0x10000

/-- `mulTail`, counting down `esi`'s high half. -/
def mulTailHi (y : Nat) : Prog isa :=
  seqs [.block [.mov .ebx (.imm 0)], half (lay full) y,
    .block [.alu .sub .esi (.imm (BitVec.ofNat 32 stepUnit)), .alu .cmp .esi (.imm (BitVec.ofNat 32 stepUnit))]]

def mulModStepHi (z y x a m t : Nat) : Prog isa :=
  seqs [mulHead (lay full) z y x t, seqs (addMod (lay full) a a t m z (t + 1)),
    seqs (addMod (lay full) x x x m z (t + 1)), mulTailHi full y]

/-- `mulMod`, for the steps in `esi`'s high half: the index in its low half is kept. -/
def mulModHi (z y x a m t : Nat) : Prog isa := .loop (mulModStepHi full z y x a m t) .ae

/-- `esi`'s high half `33`, `e`'s bits. -/
def cnt33Hi : List Instr := [.alu .add .esi (.imm (BitVec.ofNat 32 (33 * stepUnit)))]

/-- `esi`'s high half `8 q_len`, the bits of `q`'s bytes: `q_len` rotated right by 13, which for
`q_len < 2^13` is `2^19 q_len`. -/
def qBitsHi : List Instr :=
  [.mov .eax (.mem (PublicFn.argument (qLenArg full))), .shift .ror .eax 13, .alu .add .esi (.reg .eax)]

/-- Check `i`'s multiplier, multiplicand and modulus into `aY`, `aX` and `aVD`, and its steps. -/
def operands (y x m : Nat) (cnt : List Instr) : Prog isa :=
  seqs [copy (lay full) aY y, copy (lay full) aX x, copy (lay full) aVD m, .block cnt]

def choose : Prog isa :=
  .seq (.block [.alu .cmp .esi (.imm 3)]) (.ite .e (operands full aE aDP aM1 cnt33Hi)
    (.seq (.block [.alu .cmp .esi (.imm 2)]) (.ite .e (operands full aE aDQ aM2 cnt33Hi)
      (operands full aQ aQI aP (qBitsHi full)))))

/-- Check `i`: `[x] < [m]` and `[y] [x] ≡ 1 (mod [m])`. -/
def productCheck : Prog isa := seqs ([choose full] ++ ltA full aX aVD ++
  [copy (lay full) aA aZ, mulModHi full aZ aY aX aA aVD aT] ++ eqA full aA aOne ++
  [.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]])

def products : Prog isa := .seq (.block [.mov .esi (.imm 3)]) (.loop (productCheck full) .ne)

def start : Prog isa :=
  seqs ([.block (setOne (lay full) aOne), .block (bitOf (lay full) sMask aP)] ++ divSet full aN aP)

def crtChecks : Prog isa := seqs (eqA full aVQ aQ ++ eqA full aVR aZ ++
  [copy (lay full) aM1 aP, .block (clrLow (lay full) aM1), copy (lay full) aM2 aQ, .block (clrLow (lay full) aM2)] ++
  [products full])

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
