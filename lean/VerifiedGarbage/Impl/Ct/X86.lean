module

public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Impl.Scrub.X86

/-! Byte comparison with a four-byte frame holding the caller's EBX. -/

@[expose] public section

namespace VG.Impl.Ct.X86
open VG.X86

def step : List Instr := [
  .mov .eax (.mem {base := .esp, disp := 8}), .alu .add .eax (.reg .ecx),
  .movzx8 .edx {base := .eax},
  .mov .eax (.mem {base := .esp, disp := 16}), .alu .add .eax (.reg .ecx),
  .movzx8 .eax {base := .eax},
  .alu .xor .edx (.reg .eax), .alu .or .ebx (.reg .edx),
  .alu .add .ecx (.imm 1), .mov .eax (.mem {base := .esp, disp := 12}), .alu .cmp .ecx (.reg .eax)]

def finish : Prog isa := .block [.mov .eax (.reg .ebx), .alu .sub .eax (.imm 1), .shift .shr .eax 31]

def equal : Prog isa :=
  .seq (.block [.mov .ebx (.imm 0), .mov .ecx (.imm 0), .mov .eax (.mem {base := .esp, disp := 12}), .alu .cmp .ecx (.reg .eax)])
    (.seq (.ite .e (.block []) (.loop (.block step) .ne)) finish)

def body : Prog isa :=
  .seq (.block [.mov .eax (.mem {base := .esp, disp := 12}),
    .mov .edx (.mem {base := .esp, disp := 20}), .alu .cmp .eax (.reg .edx)])
    (.ite .e equal (.block [.mov .eax (.imm 0)]))

def eq : Prog isa := .frame (.push [.ebx]) body (.pop .ebx 1)
end VG.Impl.Ct.X86

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubF rb W`, or
`Impl.Scrub.X86.scrub rb` for code without a frame or calls): the `W` bytes
of stack below `esp` that its contract reserves zeroed, and the registers
a callee may change cleared but the `rb` bits of the result, so that it
returns without secret residue. -/

namespace VG.Impl.Ct.X86.Fn

open VG.X86

/-- `Spec.Ct.eqApi`'s function as emitted. -/
def eq : Prog isa :=
  Impl.Scrub.X86.scrubF 32 4 (Impl.Ct.X86.eq)

end VG.Impl.Ct.X86.Fn
