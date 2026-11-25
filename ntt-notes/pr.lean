import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Forward
import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Inverse
import VerifiedGarbage.TCB.AArch64.Print
open VG.Impl.MlKem.AArch64.Ntt16
def dump (nm : String) (b : List VG.AArch64.Instr) (r : List Nat) : IO Unit := do
  IO.println s!".globl {nm}\n.p2align 4\n{nm}:\nadrp x2, {nm}_t\nadd x2, x2, :lo12:{nm}_t"
  for i in b do for l in i.asm do IO.println l
  IO.println s!"ret\n.section .rodata\n.p2align 6\n{nm}_t:"
  for x in r do IO.println s!".hword {x}"
  IO.println ".text"
#eval do IO.println ".text"; dump "my_fwd" Forward.body Forward.rows; dump "my_inv" Inverse.body Inverse.rows; IO.println ".section .note.GNU-stack,\"\",%progbits"
#eval (Forward.body.length, Inverse.body.length, Forward.rows.length, Inverse.rows.length)
