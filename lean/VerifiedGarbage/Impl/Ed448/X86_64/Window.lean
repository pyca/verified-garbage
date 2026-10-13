module

public import VerifiedGarbage.Impl.Ed448.X86_64.WindowRegister
public import VerifiedGarbage.Impl.Ed448.SignedWindow

/-! Constant-time signed five-bit double-scalar multiplication for Ed448 verification.
The table of public-key multiples is projective, avoiding table inversions. -/

@[expose] public section

namespace VG.Impl.Ed448.X86_64.Window

open VG.X86_64 VG.Impl.Ed448
open VG.Impl.X448.X86_64 (slot BITS copyOut cswap Field)

/-- Seventeen projective points, each three 64-byte slots, within the existing scratch space. -/
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
  .seq (.block (copyOut (slot 8) (slot 6) ++ copyOut (slot 9) (slot 7) ++ store 0)) (build P 16)

def baseCoord (c : Nat) : List Instr :=
  scanCoord (fun i => chooseConst (if c = 0 then (Impl.Ed448.SignedWindow.entry i).1
    else (Impl.Ed448.SignedWindow.entry i).2)) (slot (8 + c))

def selectBase : List Instr := loadDigit BITS ++ baseCoord 0 ++ baseCoord 1

def keyCoord (c : Nat) : List Instr :=
  scanCoord (fun i => chooseMem (tabOffset i c)) (slot (8 + c))

def selectKey (o : Nat) : List Instr := loadDigit o ++ keyCoord 0 ++ keyCoord 1 ++ keyCoord 2

/-- Apply a signed digit by conditionally replacing X with -X. -/
def signFlag (o : Nat) : List Instr :=
  [.movzx8 .rax { base := .rdi, index := some .rbx, disp := ((o + 4 : Nat) : Int) },
   .alu .cmp .rax (.imm 1)]

def negateSelected (o : Nat) : Prog isa :=
  .seq (.block (constSlot 3 0)) <|
  .seq (.block (VG.Impl.X448.X86_64.sub (slot 3) (slot 3) (slot 8))) <|
  .block (VG.Impl.X448.X86_64.loads (slot 8) VG.Impl.X448.X86_64.W ++ signFlag o ++
    chooseMem (slot 3) ++ VG.Impl.X448.X86_64.stores (slot 8) VG.Impl.X448.X86_64.W)

def selectSignedBase : Prog isa := .seq (.block selectBase) (negateSelected BITS)

def selectSignedKey (o : Nat) : Prog isa := .seq (.block (selectKey o)) (negateSelected o)

/-- The projective formula differs from affine addition only in `A = Z₁Z₂`.
Form that product in the accumulator's Z slot, then reuse the affine formula's code.
The accumulator is replaced by the addition result immediately afterwards. -/
def add (F : Field) (P : Point64.Ops) : Prog isa :=
  .seq (.block (F.mul (slot 2) (slot 2) (slot 10))) P.add

def dbl5 (P : Point64.Ops) : Prog isa := .seq P.dbl (.seq P.dbl (.seq P.dbl (.seq P.dbl P.dbl)))

/-- Two scalar digits share the five doublings; both selections scan every table entry. -/
def round (F : Field) (P : Point64.Ops) (o : Nat) : Prog isa :=
  .seq (dbl5 P) <|
  .seq selectSignedBase <| .seq P.add <| .seq (.block accept) <| .seq (selectSignedKey o) <|
  .seq (add F P) (.block (accept ++ [.alu .test .rbx (.reg .rbx)]))

def step (F : Field) (P : Point64.Ops) (o : Nat) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 5)]) (round F P o)

/-- The first base-point selection is already the accumulator: no identity arithmetic. -/
def first (F : Field) (P : Point64.Ops) (o : Nat) : Prog isa :=
  .seq selectSignedBase <|
  .seq (.block (copyOut (slot 0) (slot 8) ++ copyOut (slot 1) (slot 9) ++ constSlot 2 1)) <|
  .seq (selectSignedKey o) <| .seq (add F P) (.block accept)

def joint (F : Field) (P : Point64.Ops) (o : Nat) : Prog isa :=
  .seq (table P) <| .seq (.block [.mov32 .rbx (.imm 455)]) <|
  .seq (first F P o) (.loop (step F P o) .ne)

end VG.Impl.Ed448.X86_64.Window
