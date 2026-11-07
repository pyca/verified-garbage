module

public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.TCB.Code

/-! # Compact prepared Montgomery multiplication for x86 key generation

The multiplication uses the same paired-word rows as `vg_rsa_mont_mul_at`.
Its prepared workspace follows `Proof.Rsa.Mont`: arrays 2 and 3 contain the
product, and subtraction writes the result array directly after every input
has been consumed. Saving registers on the stack leaves room for the full
product in those two arrays and avoids copying the operands to another
workspace on every Miller–Rabin square.
-/

@[expose] public section
namespace VG.Impl.Mont.X86.Compact
open VG VG.X86 VG.Impl.Mont.X86

/-- Four saved registers precede cdecl's return address and arguments. -/
def arg (i : Nat) : MemOp := at_ .esp (20 + 4 * i)

/-- Restore the other saved registers from the frame before its final pop. -/
def restoreRegs : List Instr :=
  [.mov .edi (.mem (at_ .esp 0)), .mov .esi (.mem (at_ .esp 4)), .mov .ebp (.mem (at_ .esp 8))]

end VG.Impl.Mont.X86.Compact
