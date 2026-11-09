module

public import VerifiedGarbage.Impl.Mont.AArch64

/-! # P-521 linear combinations with one Mersenne reduction -/

@[expose] public section

namespace VG.Impl.Mont.AArch64.P521Linear

open VG.AArch64

def regs : List Reg := low 9

/-- The words of `(p+1)/2^64` identify the P-521 field prime. -/
def reduction : Red := .friendly [.zero,.zero,.zero,.zero,.zero,.zero,.zero,.pow2 9,.zero]

/-- Recognize the validated reduction coefficients at code-generation time. -/
def supported (M : Mod) : Bool :=
  M.n == 9 && decide (M.red = reduction)

/-- Subtract the incoming borrow through a register list, storing each final word. -/
def correctStore : List Reg → Nat → List Instr
  | [], _ => []
  | r :: rs, o => [.sbcs .x r r .x7, st r o] ++ correctStore rs (o + 8)

/-- Detect bit 521, clear it, then subtract the complement of that carry. -/
def canonicalPrefix : List Instr :=
  [.movz .x .x3 512 0, .logic .and .x .x2 .x21 .x3, .subs .x .x2 .x2 .x3,
   .movz .x .x3 511 0, .logic .and .x .x21 .x21 .x3]

def canonicalStore (o : Nat) : List Instr := canonicalPrefix ++ correctStore regs o

def addInit : List Instr := [zero7, .subs .x .x7 .x7 .x7]

/-- Sum plus one, followed by one canonical Mersenne correction. -/
def add (o a b : Nat) : List Instr :=
  addInit ++ loads regs a ++ chain (.adcs .x) (.adcs .x) regs b ++ canonicalStore o

def maskStoreTop (o : Nat) : List Instr :=
  [.movz .x .x3 511 0, .logic .and .x .x21 .x21 .x3, st .x21 o]

def sub (o a b : Nat) : List Instr :=
  [zero7] ++ loads regs a ++ chain (.subs .x) (.sbcs .x) regs b ++
  correctStore (regs.take 8) o ++ [.sbcs .x .x21 .x21 .x7] ++ maskStoreTop (o+64)

def cmsInit (C D : Nat) : List Instr :=
  [.movz .x .x7 0 0, .subImm .x .x16 .x7 1, .movz .x .x5 0 0, .movz .x .x23 (BitVec.ofNat 16 C) 0,
   .movz .x .x22 (BitVec.ofNat 16 D) 0, .movz .x .x24 511 0]

def cmsMul (r : Reg) : List Instr :=
  [.mul .x r .x1 .x23, .umulh .x4 .x1 .x23,
     .mul .x .x6 .x2 .x22, .umulh .x17 .x2 .x22,
     .adds .x r r .x6, .adc .x .x4 .x4 .x17,
     .adds .x r r .x5, .adc .x .x5 .x4 .x7]

def cmsComplement (last : Bool) : List Instr :=
  [.bicRor .x .x2 .x16 .x2 0] ++
    (if last then [.logic .and .x .x2 .x2 .x24] else [])

def cmsRow (r : Reg) (last : Bool) (a b : Nat) : List Instr :=
  [ld .x1 a, ld .x2 b] ++ cmsComplement last ++ cmsMul r

def cmsRows : List Reg → Nat → Nat → List Instr
  | [], _, _ => []
  | r :: rs, a, b => cmsRow r rs.isEmpty a b ++ cmsRows rs (a+8) (b+8)

def cmsFoldPrefix : List Instr :=
  [.lsr .x .x2 .x21 9, .addImm .x .x2 .x2 1,
   .logic .and .x .x21 .x21 .x24, .adds .x .x8 .x8 .x2]

def cmsFold : List Instr := cmsFoldPrefix ++
  (regs.drop 1 |>.map fun r => .adcs .x r r .x7)

def cms (o C a D b : Nat) : List Instr :=
  cmsInit C D ++ cmsRows regs a b ++ cmsFold ++ canonicalStore o

end VG.Impl.Mont.AArch64.P521Linear
