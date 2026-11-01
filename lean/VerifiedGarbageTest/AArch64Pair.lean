module

import VerifiedGarbage.TCB.AArch64.Print
meta import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms

/-! Golden tests for LDP and STP of X registers, signed offset (DDI 0487 C6.2
"LDP", "STP"): the two doublewords at `n + off` and `n + off + 8`, in
little-endian order, the encodable offsets, the overlap of LDP's
destinations, the permissions, the addresses leaked, the printer, and the
registers the framework says they write. -/
namespace VG.Test.AArch64Pair
open AArch64

private def initial : State where
  gpr r := match r with
    | .x0 => 0x1000
    | .x1 => 0x1111222233334444
    | .x2 => 0x5555666677778888
    | .x6 => 0x2000
    | _ => 0
  sp := 0x8000
  -- Each byte of memory is the low byte of its address.
  mem a := BitVec.ofNat 8 a.toNat
  rd := [⟨0x1000, 520⟩]
  wr := [⟨0x2000, 64⟩]

-- `ldp x3, x4, [x0, #8]`: the doublewords at 0x1008 and 0x1010, little-endian.
#guard ((exec (.ldp .x3 .x4 .x0 8) initial).map fun s => (s.gpr .x3, s.gpr .x4, s.gpr .x0)) ==
  some (0x0f0e0d0c0b0a0908, 0x1716151413121110, 0x1000)
-- The address is computed before either register is written, so the base may
-- be one of them.
#guard ((exec (.ldp .x0 .x5 .x0 0) initial).map fun s => (s.gpr .x0, s.gpr .x5)) ==
  some (0x0706050403020100, 0x0f0e0d0c0b0a0908)
#guard ((exec (.ldp .x5 .x0 .x0 0) initial).map fun s => (s.gpr .x5, s.gpr .x0)) ==
  some (0x0706050403020100, 0x0f0e0d0c0b0a0908)
-- LDP with the same destination twice is CONSTRAINED UNPREDICTABLE: it faults.
#guard (exec (.ldp .x3 .x3 .x0 0) initial).isNone
-- Offsets: multiples of 8 up to 504 (the non-negative `imm7`).
#guard (exec (.ldp .x3 .x4 .x0 504) initial).isSome
#guard (exec (.ldp .x3 .x4 .x0 512) initial).isNone
#guard (exec (.ldp .x3 .x4 .x0 4) initial).isNone
#guard (exec (.stp .x1 .x2 .x6 512) initial).isNone
#guard (exec (.stp .x1 .x2 .x6 12) initial).isNone
-- Both doublewords must be readable: [0x1000 + 512, +16) is not.
#guard (exec (.ldp .x3 .x4 .x0 504) { initial with rd := [⟨0x1000, 519⟩] }).isNone
-- They may lie in two adjacent regions.
#guard (exec (.ldp .x3 .x4 .x0 0) { initial with rd := [⟨0x1000, 8⟩, ⟨0x1008, 8⟩] }).isSome

-- `stp x1, x2, [x6, #16]`: `x1` at 0x2010, `x2` at 0x2018, and nothing else.
#guard ((exec (.stp .x1 .x2 .x6 16) initial).map fun s =>
  (s.mem.readW 0x2010 64, s.mem.readW 0x2018 64, s.mem.readW 0x2008 64, s.mem.readW 0x2020 64,
    s.gpr .x1, s.gpr .x6)) ==
  some (0x1111222233334444, 0x5555666677778888, 0x0f0e0d0c0b0a0908, 0x2726252423222120,
    0x1111222233334444, 0x2000)
-- The same register twice is stored twice.
#guard ((exec (.stp .x1 .x1 .x6 0) initial).map fun s =>
  (s.mem.readW 0x2000 64, s.mem.readW 0x2008 64)) == some (0x1111222233334444, 0x1111222233334444)
-- Both doublewords must be writable.
#guard (exec (.stp .x1 .x2 .x0 0) initial).isNone
#guard (exec (.stp .x1 .x2 .x6 56) initial).isNone

-- The addresses of both accesses are leaked.
#guard addrs (.ldp .x3 .x4 .x0 8) initial == [0x1008, 0x1010]
#guard addrs (.stp .x1 .x2 .x6 16) initial == [0x2010, 0x2018]

#guard Instr.asm (.ldp .x3 .x4 .x0 8) == ["ldp x3, x4, [x0, #8]"]
#guard Instr.asm (.stp .x19 .x20 .x1 504) == ["stp x19, x20, [x1, #504]"]
#guard ([Instr.ldp .x3 .x4 .x0 8, .stp .x1 .x2 .x6 16].all (·.requires.isEmpty))

-- The taint analysis: a public base, and the loaded values secret.
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x0, .x3, .x4]) (.ldp .x3 .x4 .x0 8)).map
  fun τ => (AArch64.Taint.pub τ .x0, AArch64.Taint.pub τ .x3, AArch64.Taint.pub τ .x4)) ==
  some (true, false, false)
#guard (AArch64.Taint.step (AArch64.Taint.ofRegs []) (.ldp .x3 .x4 .x0 8)).isNone
#guard (AArch64.Taint.step (AArch64.Taint.ofRegs [.x6]) (.stp .x1 .x2 .x6 16)).isSome
#guard (AArch64.Taint.step (AArch64.Taint.ofRegs [.x1, .x2]) (.stp .x1 .x2 .x6 16)).isNone

-- The registers the framework says they write.
#guard dsts (.ldp .x3 .x4 .x0 8) == [.x3, .x4]
#guard dsts (.stp .x1 .x2 .x6 16) == []
#guard dstOf (.ldp .x3 .x4 .x0 8) == none
#guard [Reg.x3, .x4, .x0].map (clobbers (.ldp .x3 .x4 .x0 8)) == [true, true, false]
#guard [Reg.x1, .x2, .x6].map (clobbers (.stp .x1 .x2 .x6 16)) == [false, false, false]
#guard keeps (RegSet.ofList [.x4]) (.ldp .x3 .x4 .x0 8) == false
#guard keeps (RegSet.ofList [.x5]) (.ldp .x3 .x4 .x0 8) == true

#assert_standard_axioms VG.AArch64.exec_gpr
#assert_standard_axioms VG.AArch64.keeps_ofList
end VG.Test.AArch64Pair
