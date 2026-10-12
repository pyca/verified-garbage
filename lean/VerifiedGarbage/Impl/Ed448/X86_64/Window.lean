module

public import VerifiedGarbage.Impl.Ed448.X86_64.WindowRegister
public import VerifiedGarbage.Impl.Ed448.Window

/-! Constant-time four-bit double-scalar multiplication for Ed448 verification.
The table of public-key multiples is projective, avoiding table inversions. -/

@[expose] public section

namespace VG.Impl.Ed448.X86_64.Window

open VG.X86_64 VG.Impl.Ed448
open VG.Impl.X448.X86_64 (slot BITS copyOut cswap Field)

/-- Sixteen projective points, each three 64-byte slots, within the existing scratch space. -/
def TAB : Nat := 4096

def tabOffset (i c : Nat) : Nat := TAB + 192 * i + 64 * c

/-- Move the addition's result to the accumulator. -/
def accept : List Instr :=
  copyOut (slot 0) (slot 3) ++ copyOut (slot 1) (slot 4) ++ copyOut (slot 2) (slot 5)

def store (i : Nat) : List Instr :=
  copyOut (tabOffset i 0) (slot 0) ++ copyOut (tabOffset i 1) (slot 1) ++ copyOut (tabOffset i 2) (slot 2)

/-- Entries 1 through `n`, formed by adding the same affine point each time. -/
def build (P : Point64.Ops) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (build P n) (.seq P.add (.block (accept ++ store (n + 1))))

def table (P : Point64.Ops) : Prog isa :=
  .seq (.block (copyOut (slot 8) (slot 6) ++ copyOut (slot 9) (slot 7) ++ store 0)) (build P 15)

def baseCoord (c : Nat) : List Instr :=
  scanCoord (fun i => chooseConst (if c = 0 then (Impl.Ed448.Window.entry i).1
    else (Impl.Ed448.Window.entry i).2)) (slot (8 + c))

def selectBase : List Instr := loadDigit BITS ++ baseCoord 0 ++ baseCoord 1

def keyCoord (c : Nat) : List Instr :=
  scanCoord (fun i => chooseMem (tabOffset i c)) (slot (8 + c))

def selectKey (o : Nat) : List Instr := loadDigit o ++ keyCoord 0 ++ keyCoord 1 ++ keyCoord 2

/-- The projective formula differs from affine addition only in `A = Z₁Z₂`.
Form that product in the accumulator's Z slot, then reuse the affine formula's code.
The accumulator is replaced by the addition result immediately afterwards. -/
def add (F : Field) (P : Point64.Ops) : Prog isa :=
  .seq (.block (F.mul (slot 2) (slot 2) (slot 10))) P.add

def dbl4 (P : Point64.Ops) : Prog isa := .seq P.dbl (.seq P.dbl (.seq P.dbl P.dbl))

/-- Two scalar digits share the four doublings; both selections scan every table entry. -/
def round (F : Field) (P : Point64.Ops) (o : Nat) : Prog isa :=
  .seq (dbl4 P) <|
  .seq (.block selectBase) <| .seq P.add <| .seq (.block (accept ++ selectKey o)) <|
  .seq (add F P) (.block (accept ++ [.alu .test .rbx (.reg .rbx)]))

def step (F : Field) (P : Point64.Ops) (o : Nat) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 4)]) (round F P o)

def init : List Instr :=
  constSlot 0 0 ++ constSlot 1 1 ++ constSlot 2 1 ++ [.mov32 .rbx (.imm 456)]

def joint (F : Field) (P : Point64.Ops) (o : Nat) : Prog isa :=
  .seq (table P) (.seq (.block init) (.loop (step F P o) .ne))

end VG.Impl.Ed448.X86_64.Window
