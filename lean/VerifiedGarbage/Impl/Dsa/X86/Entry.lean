module

public import VerifiedGarbage.Impl.Dsa.X86.SignVerify

/-! # x86 cdecl entry, public-width dispatch, and register restoration

The arithmetic bodies specialize public component and digest-prefix lengths.
Only the public lengths and domain shape choose a path; acceptance checks
inside each body accumulate a mask. These programs require whole-operation
proofs before they may be emitted as API artifacts.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Entry
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Dsa.Layout

def argument (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

def savedRegisters : List (Reg × Nat) :=
  [(.ebx, Layout.saved), (.ebp, Layout.saved + 4), (.esi, Layout.saved + 8), (.edi, Layout.saved + 12)]

def save : List Instr := savedRegisters.map fun (reg, d) => .store (at_ .eax d) reg

def restore : List Instr := savedRegisters.map fun (reg, d) => .mov reg (.mem (sc d))

def saveArgument (i : Nat) (f : Field) : List Instr :=
  [.mov .eax (.mem (argument i)), .store (sc (Layout.field f)) .eax]

def addPointer (length dest : Field) : List Instr :=
  [.alu .add .eax (.mem (sc (Layout.field length))), .store (sc (Layout.field dest)) .eax]

def keyPointers : List Instr :=
  ([.mov .eax (.mem (sc (Layout.field .p)))] : List Instr) ++
    addPointer .pLen .q ++ addPointer .qLen .g ++ addPointer .pLen .y ++ addPointer .pLen .x

def saveArguments (args : List (Nat × Field)) : List Instr :=
  args.flatMap fun (i, f) => saveArgument i f

def signArguments : List (Nat × Field) :=
  [(0, .out), (2, .p), (4, .pLen), (5, .nonce), (6, .qLen), (7, .digest), (8, .digestLen)]

def verifyArguments : List (Nat × Field) :=
  [(0, .p), (2, .pLen), (3, .qLen), (4, .signature), (6, .digest), (7, .digestLen)]

def openScratch (arg : Nat) : List Instr :=
  ([.mov .eax (.mem (argument arg))] : List Instr) ++ save ++ [.mov .edi (.reg .eax)]

def signEntry : List Instr :=
  openScratch 9 ++ saveArguments signArguments ++ keyPointers

def verifyEntry : List Instr :=
  openScratch 8 ++ saveArguments verifyArguments ++ keyPointers

def failure (signing : Bool) : Prog isa :=
  if signing then Core.sequence [
    .block [.mov .esi (.mem (sc (Layout.field .out))), .mov .ecx (.mem (sc (Layout.field .qLen))),
      .alu .add .ecx (.reg .ecx), .mov .eax (.imm 0)],
    .loop (.block [.store8 (at_ .esi 0) .al, .alu .add .esi (.imm 1), .alu .sub .ecx (.imm 1)]) .ne]
  else .block [.mov .eax (.imm 0)]

/-- Static specialization is selected solely by the public digest prefix. -/
def digestDispatch (signing : Bool) (pLen qLen : Nat) : Nat → Prog isa
  | 0 => if signing then SignVerify.signBody pLen qLen 0 else SignVerify.verifyBody pLen qLen 0
  | n + 1 => .seq (.block [.mov .eax (.mem (sc (Layout.field .digestPrefixLen))),
      .alu .cmp .eax (.imm (BitVec.ofNat 32 (n + 1)))])
      (.ite .e (if signing then SignVerify.signBody pLen qLen (n + 1)
        else SignVerify.verifyBody pLen qLen (n + 1)) (digestDispatch signing pLen qLen n))

def sized (signing : Bool) (pLen qLen : Nat) : Prog isa :=
  .seq (Shape.check pLen qLen) (.ite .e (failure signing) (digestDispatch signing pLen qLen 32))

/-- Test both public widths, retaining a single fallback continuation. -/
def widthMatch (pLen qLen : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.mem (sc (Layout.field .pLen))), .alu .cmp .eax (.imm (BitVec.ofNat 32 pLen))])
    (.ite .e
      (.block [.mov .eax (.mem (sc (Layout.field .qLen))), .alu .cmp .eax (.imm (BitVec.ofNat 32 qLen))])
      (.block [.mov .eax (.imm 0), .alu .cmp .eax (.imm 1)]))

def widthDispatch (signing : Bool) : List (Nat × Nat) → Prog isa
  | [] => failure signing
  | (pLen, qLen) :: rest =>
    .seq (widthMatch pLen qLen)
      (.ite .e (sized signing pLen qLen) (widthDispatch signing rest))

def operation (signing : Bool) : Prog isa := Core.sequence [
  .block (if signing then signEntry else verifyEntry),
  widthDispatch signing [(128, 20), (256, 28), (256, 32), (384, 32)],
  .block restore]

end VG.Impl.Dsa.X86.Entry
