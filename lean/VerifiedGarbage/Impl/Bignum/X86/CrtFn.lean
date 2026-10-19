module

public import VerifiedGarbage.Impl.Bignum.X86.CrtCore

/-! # Private CRT RSA with the i686 cdecl ABI

The original components remain in backup slots while one Montgomery context
is reused for the two factors. Acceptance masks the result after computation.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def savedRegisters : List (Reg × Nat) := [(.ebx, 32), (.ebp, 36), (.esi, 40), (.edi, 44)]
def save : List Instr := savedRegisters.map fun (r, d) => .store (at_ .eax d) r
def restore : List Instr := savedRegisters.map fun (r, d) => .mov r (.mem (sc d))

def entry : List Instr :=
  [.mov .eax (.mem (PublicFn.argument 16))] ++ save ++ [.mov .edi (.reg .eax)]

def maskOutput (n : Nat) : Prog isa :=
  .seq (zerosW (slot n 5) (2 * n))
    (selectsW (2 * n) (slot n 5) (slot n resultSlot) (slot n resultSlot))

def maskResult (n : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.mem (sc acceptanceOffset))]) (maskOutput n)

def writeResult (n : Nat) : Prog isa :=
  .seq (.block PublicFn.outputArgs) (.seq (storeBE (slot n resultSlot))
    (.block [.mov .eax (.mem (sc acceptanceOffset)), .alu .and .eax (.imm 1)]))

def exportResult (n : Nat) : Prog isa := .seq (maskResult n) (writeResult n)

def sized (n : Nat) : Prog isa :=
  .seq (importComponents n) (.seq (.seq (validate n) (compute n)) (exportResult n))

def dispatch : List Nat → Prog isa
  | [] => PublicFn.failure
  | n :: rest => .seq (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 n))])
      (.ite .e (sized n) (dispatch rest))

def valid : Prog isa := .seq (.block PublicFn.widthArgs) (dispatch PublicFn.widths)

def body : Prog isa :=
  .seq (.block PublicFn.modulusArgs) (.seq (.block modulusCheck) (.ite .e valid PublicFn.failure))

def code : Prog isa := .seq (.block entry) (.seq body (.block restore))

end VG.Impl.Bignum.X86.Crt
