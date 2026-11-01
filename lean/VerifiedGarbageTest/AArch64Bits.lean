module

import VerifiedGarbage.TCB.AArch64.Print
meta import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms

/-! Baseline A64 bit counting and reversal: CLZ and RBIT on both register
widths, their printing, requirements and taint. -/

namespace VG.Test.AArch64Bits
open AArch64

private def state (a : BitVec 64) : State where
  gpr r := if r = .x1 then a else 0
  sp := 0x1000
  mem _ := 0
  rd := []
  wr := []

private def result (i : Instr) (a : BitVec 64) : Option (BitVec 64) :=
  (exec i (state a)).map fun s => s.gpr .x0

-- CLZ counts the zero bits above the highest one bit: all of them for zero.
theorem clz64 :
    result (.clz .x .x0 .x1) 0 = some 64 ∧
    result (.clz .x .x0 .x1) 1 = some 63 ∧
    result (.clz .x .x0 .x1) 0x10 = some 59 ∧
    result (.clz .x .x0 .x1) 0x8000000000000000 = some 0 := by decide

-- The W form counts within the low 32 bits.
theorem clz32 :
    result (.clz .w .x0 .x1) 0x1234567800000001 = some 31 ∧
    result (.clz .w .x0 .x1) 0xffffffff00000000 = some 32 ∧
    result (.clz .w .x0 .x1) 0x80000000 = some 0 := by decide

-- RBIT reverses the order of the bits; the W form reverses the low 32 bits and
-- clears the upper half.
theorem rbit :
    result (.rbit .x .x0 .x1) 1 = some 0x8000000000000000 ∧
    result (.rbit .x .x0 .x1) 0x0123456789abcdef = some 0xf7b3d591e6a2c480 ∧
    result (.rbit .w .x0 .x1) 0x1234567800000001 = some 0x80000000 ∧
    result (.rbit .w .x0 .x1) 0x0123456789abcdef = some 0xf7b3d591 := by decide +kernel

-- Counting trailing zeros: RBIT then CLZ.
theorem ctz :
    ((exec (.rbit .x .x0 .x1) (state 0x50)).bind (exec (.clz .x .x0 .x0))).map (·.gpr .x0) =
      some 4 := by decide +kernel

#guard Instr.asm (.clz .x .x0 .x1) == ["clz x0, x1"]
#guard Instr.asm (.clz .w .x0 .x1) == ["clz w0, w1"]
#guard Instr.asm (.rbit .x .x0 .x1) == ["rbit x0, x1"]
#guard Instr.asm (.rbit .w .x0 .x1) == ["rbit w0, w1"]

#guard ([Instr.clz .x .x0 .x1, .clz .w .x0 .x1, .rbit .x .x0 .x1, .rbit .w .x0 .x1].all
  (·.requires.isEmpty))

-- Their results are as public as their operand.
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x1]) (.clz .x .x0 .x1)).map
  (fun τ => AArch64.Taint.pub τ .x0)) == some true
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x2]) (.rbit .x .x0 .x1)).map
  (fun τ => AArch64.Taint.pub τ .x0)) == some false

end VG.Test.AArch64Bits
