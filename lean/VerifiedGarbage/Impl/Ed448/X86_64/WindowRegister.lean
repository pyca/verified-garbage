module

public import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase

/-! Register-resident constant-time coordinate scans. -/

@[expose] public section

namespace VG.Impl.Ed448.X86_64.Window

open VG.X86_64
open VG.Impl.X448.X86_64 (W sc)

/-- Read a signed five-bit magnitude once, keeping it in `r15` throughout coordinate selection. -/
def loadDigit (o : Nat) : List Instr :=
  [.movzx8 .rax { base := .rdi, index := some .rbx, disp := ((o + 3 : Nat) : Int) },
   .movzx8 .rdx { base := .rdi, index := some .rbx, disp := ((o + 2 : Nat) : Int) },
   .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rdx),
   .movzx8 .rdx { base := .rdi, index := some .rbx, disp := ((o + 1 : Nat) : Int) },
   .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rdx),
   .movzx8 .rdx { base := .rdi, index := some .rbx, disp := (o : Int) },
   .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rdx),
   .movzx8 .rdx { base := .rdi, index := some .rbx, disp := ((o - 1 : Nat) : Int) },
   .alu .add .rax (.reg .rdx),
   .movzx8 .rdx { base := .rdi, index := some .rbx, disp := ((o + 4 : Nat) : Int) },
   .mov32 .r15 (.imm 16), .alu .sub .r15 (.reg .rax),
   .alu .test .rdx (.reg .rdx), .cmov .e .r15 (.reg .rax)]

def compareDigit (i : Nat) : List Instr := [.alu .cmp .r15 (.imm (BitVec.ofNat 32 i))]

/-- Replace the seven register words exactly when the last comparison matched. -/
def chooseMem (a : Nat) : List Instr :=
  (W.zip (List.range 7)).map fun (r, i) => .cmov .e r (.mem (sc (a + 8 * i)))

def chooseConst (v : Spec.X448.Fe) : List Instr :=
  (W.zip (words7 v.val)).flatMap fun (r, x) => [.movImm64 .rax x, .cmov .e r (.reg .rax)]

/-- Every comparison and operand access has a public, fixed position. -/
def scanEntries (pick : Nat → List Instr) (xs : List Nat) : List Instr :=
  xs.flatMap fun i => compareDigit i ++ pick i

/-- Keep the selected coordinate in `W` for the entire scan, then store it once. -/
def scanCoord (pick : Nat → List Instr) (o : Nat) : List Instr :=
  scanEntries pick (List.range 17) ++ VG.Impl.X448.X86_64.stores o W

end VG.Impl.Ed448.X86_64.Window
