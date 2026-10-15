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

def keyPointers : List Instr :=
  [.mov .eax (.mem (sc (Layout.field .p))), .alu .add .eax (.mem (sc (Layout.field .pLen))),
    .store (sc (Layout.field .q)) .eax, .alu .add .eax (.mem (sc (Layout.field .qLen))),
    .store (sc (Layout.field .g)) .eax, .alu .add .eax (.mem (sc (Layout.field .pLen))),
    .store (sc (Layout.field .y)) .eax, .alu .add .eax (.mem (sc (Layout.field .pLen))),
    .store (sc (Layout.field .x)) .eax]

def signEntry : List Instr :=
  ([.mov .eax (.mem (argument 9))] : List Instr) ++ save ++
  ([.mov .edi (.reg .eax), .mov .eax (.imm 0), .store (sc (Layout.field .signature)) .eax] : List Instr) ++
  saveArgument 0 .out ++ saveArgument 2 .p ++ saveArgument 4 .pLen ++ saveArgument 5 .nonce ++
  saveArgument 6 .qLen ++ saveArgument 7 .digest ++ saveArgument 8 .digestLen ++ keyPointers

def verifyEntry : List Instr :=
  ([.mov .eax (.mem (argument 8))] : List Instr) ++ save ++
  ([.mov .edi (.reg .eax), .mov .eax (.imm 0), .store (sc (Layout.field .out)) .eax,
    .store (sc (Layout.field .nonce)) .eax] : List Instr) ++
  saveArgument 0 .p ++ saveArgument 2 .pLen ++ saveArgument 3 .qLen ++ saveArgument 4 .signature ++
  saveArgument 6 .digest ++ saveArgument 7 .digestLen ++ keyPointers

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

def widthDispatch (signing : Bool) : List (Nat × Nat) → Prog isa
  | [] => failure signing
  | (pLen, qLen) :: rest =>
    .seq (.block [.mov .eax (.mem (sc (Layout.field .pLen))), .alu .cmp .eax (.imm (BitVec.ofNat 32 pLen))])
      (.ite .e
        (.seq (.block [.mov .eax (.mem (sc (Layout.field .qLen))), .alu .cmp .eax (.imm (BitVec.ofNat 32 qLen))])
          (.ite .e (sized signing pLen qLen) (widthDispatch signing rest)))
        (widthDispatch signing rest))

def operation (signing : Bool) : Prog isa := Core.sequence [
  .block (if signing then signEntry else verifyEntry),
  widthDispatch signing [(128, 20), (256, 28), (256, 32), (384, 32)],
  .block restore]

end VG.Impl.Dsa.X86.Entry
