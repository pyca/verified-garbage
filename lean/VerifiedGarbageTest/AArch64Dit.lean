module

import VerifiedGarbage.TCB.AArch64.Encode
meta import VerifiedGarbage.TCB.AArch64.Encode
import VerifiedGarbage.TCB.AArch64.Print
meta import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# PSTATE.DIT: `mrsDit` and `msrDitImm`

Reading PSTATE.DIT through the system register DIT, whose bit 24 it is (DDI
0601 2026-03, "DIT, Data Independent Timing"), and writing it with MSR
(immediate): their semantics, their text, their machine code, the feature
they require and their taint.
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

-- MSR sets PSTATE.DIT to its immediate, whatever it was, and changes no
-- register.
#guard [false, true].all fun d => [false, true].all fun on =>
  run (.msrDitImm on) d 0x1000000 == some (on, 0xffffffffffffffff)

-- Enabling it and reading what it was: `mrs` then `msr DIT, #1`.
#guard [false, true].all fun d =>
  ((exec (.mrsDit .x0) (state d 0)).bind (exec (.msrDitImm true))).map
    (fun s => (s.dit, s.gpr .x0)) == some (true, if d then 0x1000000 else 0)

-- No other instruction reads or writes it.
#guard [false, true].all fun d =>
  [Instr.add .x .x0 .x1 .x1, .mul .x .x0 .x1 .x1, .tst .x .x1 .x1, .align 4].all fun i =>
    (exec i (state d 0x1000000)).map (·.dit) == some d
#guard [false, true].all fun d => (isa.call (state d 0)).map (·.dit) == some d

#guard Instr.asm (.mrsDit .x0) == ["mrs x0, DIT"]
#guard Instr.asm (.mrsDit .x17) == ["mrs x17, DIT"]
#guard Instr.asm (.msrDitImm true) == ["msr DIT, #1"]
#guard Instr.asm (.msrDitImm false) == ["msr DIT, #0"]

#guard Instr.encode (.mrsDit .x0) == some [0xD53B42A0]
#guard Instr.encode (.mrsDit .x17) == some [0xD53B42B1]
#guard Instr.encode (.msrDitImm true) == some [0xD503415F]
#guard Instr.encode (.msrDitImm false) == some [0xD503405F]

#guard isa.requires (.mrsDit .x0) == ["dit"]
#guard isa.requires (.msrDitImm true) == ["dit"]

-- PSTATE.DIT is not tracked: what MRS reads is secret, and MSR changes no
-- register's taint.
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x0, .x1]) (.mrsDit .x0)).map
  (fun τ => (AArch64.Taint.pub τ .x0, AArch64.Taint.pub τ .x1))) == some (false, true)
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x1]) (.msrDitImm true)).map
  (fun τ => (AArch64.Taint.pub τ .x0, AArch64.Taint.pub τ .x1))) == some (false, true)

end VG.Test.AArch64Dit
