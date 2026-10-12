import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase
import VerifiedGarbage.Impl.Ed448.Window

/-! Constant-time four-bit double-scalar multiplication for Ed448 verification.
The table of public-key multiples is projective, avoiding table inversions. -/
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

/-- Compare a nibble from expanded bits at `o + rbx` with the public index `i`. -/
def digitMask (o i : Nat) : List Instr :=
  [.movzx8 .rax { base := .rdi, index := some .rbx, disp := ((o + 3 : Nat) : Int) },
   .movzx8 .rdx { base := .rdi, index := some .rbx, disp := ((o + 2 : Nat) : Int) },
   .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rdx),
   .movzx8 .rdx { base := .rdi, index := some .rbx, disp := ((o + 1 : Nat) : Int) },
   .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rdx),
   .movzx8 .rdx { base := .rdi, index := some .rbx, disp := (o : Int) },
   .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rdx),
   .alu .xor .rax (.imm (BitVec.ofNat 32 i)), .alu .cmp .rax (.imm 1),
   .mov32 .rcx (.imm 0), .alu .sbb .rcx (.reg .rcx)]

def baseEntry (i : Nat) : List Instr :=
  constSlot 3 (Impl.Ed448.Window.entry i).1 ++ constSlot 4 (Impl.Ed448.Window.entry i).2 ++
  digitMask BITS i ++ cswap (slot 8) (slot 3) ++ cswap (slot 9) (slot 4)

def selectBase : List Instr := (List.range 16).flatMap baseEntry

def loadEntry (i : Nat) : List Instr :=
  copyOut (slot 3) (tabOffset i 0) ++ copyOut (slot 4) (tabOffset i 1) ++ copyOut (slot 5) (tabOffset i 2)

def keyEntry (o i : Nat) : List Instr :=
  loadEntry i ++ digitMask o i ++ cswap (slot 8) (slot 3) ++ cswap (slot 9) (slot 4) ++ cswap (slot 10) (slot 5)

def selectKey (o : Nat) : List Instr := (List.range 16).flatMap (keyEntry o)

/-- The full projective addition, using the existing field operations. -/
def add (F : Field) : Prog isa :=
  .block (fieldCode F (addOps.take 4) ++ Point64.mulD ++ fieldCode F (addOps.drop 5))

def dbl4 (P : Point64.Ops) : Prog isa := .seq P.dbl (.seq P.dbl (.seq P.dbl P.dbl))

/-- Two scalar digits share the four doublings; both selections scan every table entry. -/
def round (F : Field) (P : Point64.Ops) (o : Nat) : Prog isa :=
  .seq (dbl4 P) <|
  .seq (.block selectBase) <| .seq P.add <| .seq (.block (accept ++ selectKey o)) <|
  .seq (add F) (.block (accept ++ [.alu .test .rbx (.reg .rbx)]))

def step (F : Field) (P : Point64.Ops) (o : Nat) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 4)]) (round F P o)

def init : List Instr :=
  constSlot 0 0 ++ constSlot 1 1 ++ constSlot 2 1 ++ [.mov32 .rbx (.imm 456)]

def joint (F : Field) (P : Point64.Ops) (o : Nat) : Prog isa :=
  .seq (table P) (.seq (.block init) (.loop (step F P o) .ne))

end VG.Impl.Ed448.X86_64.Window
