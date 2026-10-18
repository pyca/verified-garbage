module

public import VerifiedGarbage.Impl.Dsa.Arm.SignVerify

/-! # AAPCS entry, public-width dispatch and register restoration on ARM

The arguments are `r0`–`r3` and then words on the stack. The entry saves
`r4`–`r11` and `lr` in the header of `scratch`, whose address it keeps in
`r12`, and the arguments the bodies use; the exit restores them. Only the
public lengths and domain shape choose a path; acceptance checks inside each
body accumulate a mask. `operation true` and `operation false` are
`vg_dsa_sign` and `vg_dsa_verify`.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.Entry
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Dsa.Layout

/-- The registers saved at `[saved + 4i]`. -/
def savedRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

def save : List Instr := savedRegs.zipIdx.map fun (r, i) => .str r .r12 (Layout.saved + 4 * i)

def restore : List Instr := savedRegs.zipIdx.map fun (r, i) => .ldr r .r12 (Layout.saved + 4 * i)

/-- A register argument, or the stack word at `sp + 4i`. -/
inductive Arg where
  | reg (r : Reg)
  | stack (i : Nat)
  deriving DecidableEq, Repr

def saveArgument : Arg × Field → List Instr
  | (.reg r, f) => [.str r .r12 (Layout.field f)]
  | (.stack i, f) => [.ldrSp .r4 (4 * i), .str .r4 .r12 (Layout.field f)]

def addPointer (length dest : Field) : List Instr :=
  [.ldr .r5 .r12 (Layout.field length), .dp .add .r4 .r4 (.reg .r5), .str .r4 .r12 (Layout.field dest)]

def keyPointers : List Instr :=
  [.ldr .r4 .r12 (Layout.field .p)] ++
    addPointer .pLen .q ++ addPointer .qLen .g ++ addPointer .pLen .y ++ addPointer .pLen .x

def signArguments : List (Arg × Field) :=
  [(.reg .r0, .out), (.reg .r2, .p), (.stack 0, .pLen), (.stack 1, .nonce), (.stack 2, .qLen),
    (.stack 3, .digest), (.stack 4, .digestLen)]

def verifyArguments : List (Arg × Field) :=
  [(.reg .r0, .p), (.reg .r2, .pLen), (.reg .r3, .qLen), (.stack 0, .signature), (.stack 2, .digest),
    (.stack 3, .digestLen)]

/-- `r12 = scratch` (the stack argument `i`), and the registers saved. -/
def openScratch (i : Nat) : List Instr := [.ldrSp .r12 (4 * i)] ++ save

def signEntry : List Instr :=
  openScratch 5 ++ signArguments.flatMap saveArgument ++ keyPointers

def verifyEntry : List Instr :=
  openScratch 4 ++ verifyArguments.flatMap saveArgument ++ keyPointers

def failure (signing : Bool) : Prog isa :=
  if signing then Core.sequence [
    .block [.ldr .r11 .r12 (Layout.field .out), .ldr .r4 .r12 (Layout.field .qLen),
      .dp .add .lr .r11 (.reg .r4), .dp .add .lr .lr (.reg .r4), .mov .r4 (.imm 0)],
    .loop (.block [.strb .r4 .r11 0, .dp .add .r11 .r11 (.imm 1), .cmp .r11 (.reg .lr)]) .ne,
    .block [.mov .r0 (.imm 0)]]
  else .block [.mov .r0 (.imm 0)]

def sized (signing : Bool) (pLen qLen : Nat) : Prog isa :=
  .seq (Shape.check pLen qLen)
    (.ite .eq (failure signing) (if signing then SignVerify.signBody pLen qLen else SignVerify.verifyBody pLen qLen))

/-- Test both public widths, retaining a single fallback continuation. -/
def widthMatch (pLen qLen : Nat) : Prog isa :=
  .seq (.block [.ldr .r4 .r12 (Layout.field .pLen), .movw .r5 (BitVec.ofNat 16 pLen), .cmp .r4 (.reg .r5)])
    (.ite .eq
      (.block [.ldr .r4 .r12 (Layout.field .qLen), .movw .r5 (BitVec.ofNat 16 qLen), .cmp .r4 (.reg .r5)])
      (.block [.mov .r4 (.imm 0), .cmp .r4 (.imm 1)]))

def widthDispatch (signing : Bool) : List (Nat × Nat) → Prog isa
  | [] => failure signing
  | (pLen, qLen) :: rest =>
    .seq (widthMatch pLen qLen)
      (.ite .eq (sized signing pLen qLen) (widthDispatch signing rest))

def operation (signing : Bool) : Prog isa := Core.sequence [
  .block (if signing then signEntry else verifyEntry),
  widthDispatch signing [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)],
  .block restore]

end VG.Impl.Dsa.Arm.Entry
