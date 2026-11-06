module

public import VerifiedGarbage.Spec.Rc2
public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Constant-time RC2 selection on baseline x86-64

All candidates are visited in a fixed order. The secret index is compared
with each public candidate using arithmetic, never used as an address or
branch condition. Subtracting one from `x XOR i` borrows exactly when
`x = i`; `sbb r10, r10` turns that borrow into the selection mask.
-/

@[expose] public section

namespace VG.Impl.Rc2.X86_64

open VG.X86_64

def memOp (base : Reg) (offset : Nat) : MemOp := { base, disp := Int.ofNat offset }
def rr (dst src : Reg) : Instr := .mov dst (.reg src)
def imm (dst : Reg) (n : Nat) : Instr := .mov dst (.imm (BitVec.ofNat 32 n))

/-- Load a little-endian 16-bit word at the public offset `2*i` of `rdi`
into `r8`. Byte loads avoid reading past the last schedule word. -/
def loadKey (i : Nat) : List Instr :=
  [.movzx8 .r8 (memOp .rdi (2 * i)), .movzx8 .r9 (memOp .rdi (2 * i + 1)),
   .shift .ror .r9 56, .alu .or .r8 (.reg .r9)]

end VG.Impl.Rc2.X86_64
