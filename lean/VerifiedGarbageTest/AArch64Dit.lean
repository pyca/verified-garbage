module

import VerifiedGarbage.TCB.AArch64.Encode
meta import VerifiedGarbage.TCB.AArch64.Encode
import VerifiedGarbage.TCB.AArch64.Print
meta import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# PSTATE.DIT: `mrsDit` and `msrDit`

Reading and writing PSTATE.DIT through the system register DIT, whose bit 24
it is (DDI 0601 2026-03, "DIT, Data Independent Timing"): their semantics,
their text, their machine code, the feature they require and their taint.
The words are LLVM 18.1.3's for the printed text (`llvm-mc -triple=aarch64
-mattr=+dit -show-encoding`), which without `+dit` refuses it ("expected
writable system register or pstate").
-/

namespace VG.Test.AArch64Dit

open AArch64

private def state (dit : Bool) (a : BitVec 64) : State where
  gpr r := if r = .x1 then a else 0xffffffffffffffff
  sp := 0x1000
  mem _ := 0
  rd := []
  wr := []
  dit := dit

/-- PSTATE.DIT and `x0` after `i`. -/
private def run (i : Instr) (dit : Bool) (a : BitVec 64) : Option (Bool × BitVec 64) :=
  (exec i (state dit a)).map fun s => (s.dit, s.gpr .x0)

-- MRS gives PSTATE.DIT in bit 24, and zeros in every other bit.
#guard run (.mrsDit .x0) true 0 == some (true, 0x1000000)
#guard run (.mrsDit .x0) false 0 == some (false, 0)

-- MSR sets PSTATE.DIT to bit 24 of its register, whatever the other bits.
#guard run (.msrDit .x1) false 0x1000000 == some (true, 0xffffffffffffffff)
#guard run (.msrDit .x1) false 0xffffffffffffffff == some (true, 0xffffffffffffffff)
#guard run (.msrDit .x1) true 0 == some (false, 0xffffffffffffffff)
#guard run (.msrDit .x1) true 0xfffffffffeffffff == some (false, 0xffffffffffffffff)

-- What MRS read, MSR writes back: the save and restore of a caller's value.
#guard [false, true].all fun d =>
  ((exec (.mrsDit .x1) (state d 0)).bind fun s =>
    (exec (.msrDit .x1) { s with dit := !d }).map (·.dit)) == some d

-- No other instruction reads or writes it.
#guard [false, true].all fun d =>
  [Instr.add .x .x0 .x1 .x1, .mul .x .x0 .x1 .x1, .tst .x .x1 .x1, .align 4].all fun i =>
    (exec i (state d 0x1000000)).map (·.dit) == some d
#guard [false, true].all fun d => (isa.call (state d 0)).map (·.dit) == some d

#guard Instr.asm (.mrsDit .x0) == ["mrs x0, DIT"]
#guard Instr.asm (.mrsDit .x17) == ["mrs x17, DIT"]
#guard Instr.asm (.msrDit .x0) == ["msr DIT, x0"]
#guard Instr.asm (.msrDit .x16) == ["msr DIT, x16"]

#guard Instr.encode (.mrsDit .x0) == some [0xD53B42A0]
#guard Instr.encode (.mrsDit .x17) == some [0xD53B42B1]
#guard Instr.encode (.msrDit .x0) == some [0xD51B42A0]
#guard Instr.encode (.msrDit .x16) == some [0xD51B42B0]

#guard isa.requires (.mrsDit .x0) == ["dit"]
#guard isa.requires (.msrDit .x0) == ["dit"]

-- PSTATE.DIT is not tracked: what MRS reads is secret, and MSR changes no
-- register's taint.
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x0, .x1]) (.mrsDit .x0)).map
  (fun τ => (AArch64.Taint.pub τ .x0, AArch64.Taint.pub τ .x1))) == some (false, true)
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x1]) (.msrDit .x0)).map
  (fun τ => (AArch64.Taint.pub τ .x0, AArch64.Taint.pub τ .x1))) == some (false, true)

end VG.Test.AArch64Dit
