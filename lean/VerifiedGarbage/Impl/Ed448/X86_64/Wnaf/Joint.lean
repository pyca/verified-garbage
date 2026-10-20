module

public import VerifiedGarbage.Impl.Ed448.X86_64.Wnaf.Recode
public import VerifiedGarbage.Impl.Ed448.X86_64.Window

/-! Sparse public double-scalar multiplication, reusing the proved point formulas. -/

@[expose] public section

namespace VG.Impl.Ed448.X86_64.Wnaf
open VG.X86_64
open VG.Impl.Ed448.X86_64
open VG.Impl.X448.X86_64 (slot W loads stores Field)

def getDigit (o : Nat) : List Instr :=
  [.movzx8 .r15 { base := .rdi, index := some .rbx, disp := (o : Int) },
   .alu .test .r15 (.reg .r15)]

def magnitude : List Instr :=
  [.mov32 .rax (.imm 256), .alu .sub .rax (.reg .r15), .alu .cmp .r15 (.imm 128),
   .cmov .ae .r15 (.reg .rax)]

def signFlag (o : Nat) : List Instr :=
  [.movzx8 .rax { base := .rdi, index := some .rbx, disp := (o : Int) },
   .alu .and .rax (.imm 128), .alu .cmp .rax (.imm 128)]

def negateSelected (o : Nat) : Prog isa :=
  .seq (.block (constSlot 3 0)) <|
  .seq (.block (VG.Impl.X448.X86_64.sub (slot 3) (slot 3) (slot 8))) <|
  .block (loads (slot 8) W ++ signFlag o ++ Window.chooseMem (slot 3) ++ stores (slot 8) W)

def selectBase : Prog isa :=
  .seq (.block (magnitude ++ Window.baseCoord 0 ++ Window.baseCoord 1)) (negateSelected SDIG)

def selectKey : Prog isa :=
  .seq (.block (magnitude ++ Window.keyAddress ++ Window.directKeyCoord 0 ++
    Window.directKeyCoord 1 ++ Window.directKeyCoord 2)) (negateSelected KDIG)

def addBase (P : Point64.Ops) : Prog isa :=
  .seq (.block (getDigit SDIG)) <|
  .ite .ne (.seq selectBase (.seq P.add (.block Window.accept))) (.block [])

def addKey (F : Field) (P : Point64.Ops) : Prog isa :=
  .seq (.block (getDigit KDIG)) <|
  .ite .ne (.seq selectKey (.seq (Window.add F P) (.block Window.accept))) (.block [])

def step (F : Field) (P : Point64.Ops) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq P.dbl <| .seq (addBase P) <| .seq (addKey F P) <|
  .block [.alu .test .rbx (.reg .rbx)]

def joint (F : Field) (P : Point64.Ops) (o : Nat) : Prog isa :=
  .seq (Window.table P) <|
  .seq (recode VG.Impl.X448.X86_64.BITS SDIG) <|
  .seq (recode o KDIG) <|
  .seq (.block (constSlot 0 0 ++ constSlot 1 1 ++ constSlot 2 1 ++ [.mov32 .rbx (.imm 461)])) <|
  .loop (step F P) .ne

end VG.Impl.Ed448.X86_64.Wnaf
