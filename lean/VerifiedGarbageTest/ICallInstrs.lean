module

import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# The instructions of indirect calls (`ISA.icall`) on x86, AArch64, ARMv7, PPC64LE and RISC-V

As x86-64's `callr` in `FnTablesX86_64.lean`: each model's instruction of an
indirect call prints as its manual's mnemonic and encodes as its manual's
bytes (x86: SDM Vol. 2, "CALL", `FF /2`; AArch64: DDI 0487, C6.2 "BLR";
PPC64LE: Book I, "mtspr" with `SPR = 9` and "bcctr" with `BO = 20`, `LK =
1`, the words GNU as writes for `mtctr 12` and `bctrl`; RISC-V: RV32I,
"Unconditional Jumps", `JALR` with `rd = ra`, the word GNU as writes for
`jalr t1`), and calls the
address in its register.
-/

namespace VG

#guard X86.Instr.asm (.callr .eax) == ["call eax"]
#guard X86.Instr.encode (.callr .eax) == some [[0xFF, 0xD0]]
#guard X86.Instr.encode (.callr .esi) == some [[0xFF, 0xD6]]

#guard AArch64.Instr.asm (.blr .x16) == ["blr x16"]
#guard AArch64.Instr.encode (.blr .x16) == some [0xD63F0200]
#guard AArch64.Instr.encode (.blr .x8) == some [0xD63F0100]

#guard Arm.Instr.asm (.blx .r12) == ["blx r12"]

#guard PPC64LE.Instr.asm .bctrl == ["mtctr %r12", "bctrl"]
#guard PPC64LE.Instr.encode .bctrl == some [0x7D8903A6, 0x4E800421]

#guard RISCV64.Instr.asm (.jalr .t1) == ["jalr ra, 0(t1)"]
#guard RISCV64.Instr.encode (.jalr .t1) == some [0x000300E7]

example (s : X86.State) : X86.isa.icall (.callr .ecx) s = some ((s.gpr .ecx).setWidth 64) := rfl
example (s : AArch64.State) : AArch64.isa.icall (.blr .x9) s = some (s.gpr .x9) := rfl
example (s : Arm.State) : Arm.isa.icall (.blx .r3) s = some ((s.gpr .r3).setWidth 64) := rfl
example (s : PPC64LE.State) : PPC64LE.isa.icall .bctrl s = some (s.gpr .r12) := rfl
example (s : RISCV64.State) : RISCV64.isa.icall (.jalr .t1) s = some (s.gpr .t1) := rfl

end VG
