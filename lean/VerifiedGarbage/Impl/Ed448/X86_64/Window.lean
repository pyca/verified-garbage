module

public import VerifiedGarbage.Impl.Ed448.X86_64.WindowRegister
public import VerifiedGarbage.Impl.Ed448.SignedWindow

/-! Signed five-bit double-scalar multiplication for Ed448 verification.
The table of public-key multiples is projective, avoiding table inversions.
Verification digits are public and index that table directly. -/

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

/-- Public verification digit scaled to its 192-byte table entry. -/
def keyAddress : List Instr :=
  [.mov .rax (.reg .r15), .mov32 .rdx (.imm 192), .mul .rdx, .mov .r15 (.reg .rax)]

/-- Read only the selected public-key coordinate. -/
def directKeyCoord (c : Nat) : List Instr :=
  ((VG.Impl.X448.X86_64.W.zip (List.range 7)).map fun (r, i) =>
    .mov r (.mem { base := .rdi, index := some .r15, disp := ((TAB + 64 * c + 8 * i : Nat) : Int) })) ++
  VG.Impl.X448.X86_64.stores (slot (8 + c)) VG.Impl.X448.X86_64.W

/-- The projective formula differs from affine addition only in `A = Z₁Z₂`.
Form that product in the accumulator's Z slot, then reuse the affine formula's code.
The accumulator is replaced by the addition result immediately afterwards. -/
def add (F : Field) (P : Point64.Ops) : Prog isa :=
  .seq (.block (F.mul (slot 2) (slot 2) (slot 10))) P.add

end VG.Impl.Ed448.X86_64.Window
