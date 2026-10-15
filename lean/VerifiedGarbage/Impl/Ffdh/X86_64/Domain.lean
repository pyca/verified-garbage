module

public import VerifiedGarbage.Impl.Rsa.X86_64.Crt
public import VerifiedGarbage.Impl.Rsa.X86_64.Keys

/-!
# FFDH on x86-64: workspace and comparisons

The outer workspace holds the arguments and eight arrays. Its end is the
inner Montgomery workspace, followed by the 32-entry exponentiation table.
The header slots match the AArch64 domain implementation; slots 0–5 save
System V's callee-saved registers. Comparisons examine every word and
return a Boolean in `rax`, without branching on the operands.
-/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.Domain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK)
open VG.Impl.Rsa.X86_64.Crt (ws wsEnd wsNew loadArr copyArr zeroArr leave)

def sDom : Nat := sFn 0
def sDomLen : Nat := sFn 1
def sY : Nat := sFn 3
def sX : Nat := sFn 4
def sXl : Nat := sFn 5
def sOut : Nat := sFn 6
def sEp : Nat := sFn 7
def sEl : Nat := sFn 8
def sRand : Nat := sFn 9
def sXe : Nat := sFn 10
def sG : Nat := sFn 11
def sQ : Nat := sFn 12
def sWs : Nat := sFn 13
def sF : Nat := sFn 14
def sMsk : Nat := sFn 15

/-- Enter the inner workspace. -/
def enter : Instr := .mov .rdi (.mem (hdr sWs))

/-- Allocate the inner workspace after the outer arrays, retaining the
outer base in `rdi`. -/
def wsSetup (sl : Nat) : List (Prog isa) :=
  [.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ wsEnd)] ++ wsNew sWs sl

/-- The modulus, its negative word inverse, and the constant one. -/
def modSetup (sp sl : Nat) : List (Prog isa) :=
  loadArr aN sp sl ++
  [.block (([.mov .rbx (.mem (hdr (sArr aN))), .mov .rbx (.mem (at0 .rbx))] : List Instr) ++ minv ++
    [.store (hdr sMinv) .r15, .mov .r12 (.mem (hdr sW)), .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]),
    setWord aOne .rcx]

/-- Enter and initialize the workspace for p. -/
def pSetup : List (Prog isa) := wsSetup sK ++ [.block [enter]] ++ modSetup sDom sK

/-- Fixed-window exponentiation `ex` over every exponent byte. Keep R² in
`aX` while the exponentiation uses its usual base array. -/
def pow (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa))
    (bp bl ep el : Nat) : List (Prog isa) :=
  loadArr aXm bp bl ++ [mul aY aR2 aOne, mul aXm aXm aR2] ++ copyArr aX aR2 ++
  copyArr Crt.aXc aXm ++ ex ep el ++ [mul aY aY aOne] ++ copyArr aR2 aX

/-- The array pointers and public word count for a comparison. -/
def ptrs (a b : Nat) : List Instr :=
  [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr a))), .mov .r10 (.mem (hdr (sArr b))),
    .mov32 .rbp (.imm 0)]

/-- The borrow mask of `[a] - [b]` in `rbp`, without storing the difference. -/
def cmpArr (a b : Nat) : List (Prog isa) :=
  [.block (ptrs a b), wordLoop 0
    [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp]]

/-- `rax := [a] < [b]`. -/
def ltArr (a b : Nat) : List (Prog isa) :=
  cmpArr a b ++ [.block [.mov .rax (.reg .rbp), .alu .and .rax (.imm 1)]]

/-- `rax := [a] >= [b]`. -/
def geArr (a b : Nat) : List (Prog isa) :=
  cmpArr a b ++ [.block [.mov .rax (.reg .rbp), .alu .and .rax (.imm 1), .alu .xor .rax (.imm 1)]]

/-- `rax := [a] = [b]`, from the OR of all wordwise XORs. -/
def eqArr (a b : Nat) : List (Prog isa) :=
  [.block (ptrs a b), wordLoop 0 Keys.xorBody,
    .block [.alu .cmp .rbp (.imm 1), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 1)]]

def gt1 (a : Nat) : List (Prog isa) := ltArr aOne a
def isOne (a : Nat) : List (Prog isa) := eqArr a aOne
def isZero (a : Nat) : List (Prog isa) := ltArr a aOne
def isNonzero (a : Nat) : List (Prog isa) := geArr a aOne

/-- `[a]` with its low bit set, compared with the odd modulus: this tests
`[a] < p - 1` without changing the modulus. -/
def ltP (a : Nat) : List (Prog isa) :=
  copyArr aTmp a ++ [.block [.mov .rbx (.mem (hdr (sArr aTmp)))], .block [.mov .rax (.mem (at0 .rbx)),
    .alu .or .rax (.imm 1), .store (at0 .rbx) .rax]] ++ ltArr aTmp aN

/-- The low bit, independent of the other words. -/
def isOdd (a : Nat) : List (Prog isa) :=
  [.block [.mov .rbx (.mem (hdr (sArr a))), .mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1)]]

/-- Conjoin the Boolean with the saved flag and save the result. -/
def andF : List Instr := [.alu .and .rax (.mem (hdr sF)), .store (hdr sF) .rax]

def range (a : Nat) : List (Prog isa) :=
  gt1 a ++ [.block [.store (hdr sF) .rax]] ++ ltP a ++ [.block andF]

end VG.Impl.Ffdh.X86_64.Domain
