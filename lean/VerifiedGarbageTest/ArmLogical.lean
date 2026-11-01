module

import VerifiedGarbage.TCB.Arm.Print
meta import VerifiedGarbage.TCB.Arm.Print
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-!
# ARMv7 MVN and BIC semantics and printing

The reference pseudocode is Arm ARM DDI 0406C's MVN/BIC immediate and
register instructions, with S = 0. The printed instructions and model
results are also compared with Keystone 0.9.2 and Unicorn 2.1.4 in A32
and T32 modes (3822 comparisons and 78 printed encodings per mode),
emulating Cortex-A15; this is emulator validation, not a
measurement on Arm hardware. Include immediate and shifted forms,
source/destination aliases, preserved flags, and rejected operands.
-/

namespace VG.Test.ArmLogical
open VG.Arm

def s : State where
  gpr r := if r = .r1 then 0x12345678 else if r = .r2 then 0x0f0f0f0f else 0xdeadbeef
  sp := 0x1000
  n := true
  z := false
  c := true
  v := true
  mem _ := 0
  rd := []
  wr := []

def result (i : Instr) (d : Reg := .r0) : Option (BitVec 32) := (exec i s).map (·.gpr d)

#guard result (.mvn .r0 (.reg .r1)) == some 0xedcba987
#guard result (.mvn .r1 (.reg .r1)) .r1 == some 0xedcba987
#guard result (.mvn .r0 (.imm 0)) == some 0xffffffff
#guard result (.mvn .r0 (.imm 0x80000000)) == some 0x7fffffff
#guard result (.mvn .r0 (.shifted .r1 .lsl 8)) == some 0xcba987ff
#guard result (.mvn .r0 (.shifted .r1 .lsr 8)) == some 0xffedcba9
#guard result (.mvn .r0 (.shifted .r1 .ror 8)) == some 0x87edcba9
#guard result (.mvn .r0 (.reg .lr)) == some 0x21524110
#guard result (.dp .bic .r0 .r1 (.reg .r2)) == some 0x10305070
#guard result (.dp .bic .r1 .r1 (.reg .r2)) .r1 == some 0x10305070
#guard result (.dp .bic .r2 .r1 (.reg .r2)) .r2 == some 0x10305070
#guard result (.dp .bic .r0 .r1 (.imm 255)) == some 0x12345600
#guard result (.dp .bic .r0 .r1 (.shifted .r2 .lsl 4)) == some 0x02040608

#guard (exec (.mvn .r0 (.imm 0x12345678)) s).isNone
#guard (exec (.dp .bic .r0 .r1 (.imm 0x12345678)) s).isNone
#guard (exec (.mvn .r0 (.shifted .r1 .ror 0)) s).isNone
#guard (exec (.mvn .r0 (.shifted .r1 .lsl 32)) s).isNone

#guard ([Instr.mvn .r0 (.reg .r1), .dp .bic .r0 .r1 (.reg .r2)]).all fun i =>
  (exec i s).map (fun t => (t.n, t.z, t.c, t.v, t.gpr .r1, t.gpr .r2, t.sp)) ==
    some (true, false, true, true, 0x12345678, 0x0f0f0f0f, 0x1000)

#guard printer.instr (.mvn .r0 (.reg .r1)) == ["mvn r0, r1"]
#guard printer.instr (.mvn .r10 (.shifted .lr .ror 1)) == ["mvn r10, lr, ror #1"]
#guard printer.instr (.dp .bic .r0 .r1 (.reg .r2)) == ["bic r0, r1, r2"]
#guard printer.instr (.dp .bic .r0 .r1 (.imm 255)) == ["bic r0, r1, #255"]
#guard isa.requires (.mvn .r0 (.reg .r1)) == []
#guard isa.requires (.dp .bic .r0 .r1 (.reg .r2)) == []

#guard (VG.Arm.Taint.step (VG.Arm.Taint.ofRegs [.r1]) (.mvn .r0 (.reg .r1))).map (fun t => VG.Arm.Taint.pub t .r0) == some true
#guard (VG.Arm.Taint.step (VG.Arm.Taint.ofRegs []) (.mvn .r0 (.reg .r1))).map (fun t => VG.Arm.Taint.pub t .r0) == some false
#guard (VG.Arm.Taint.step (VG.Arm.Taint.ofRegs [.r1, .r2]) (.dp .bic .r0 .r1 (.reg .r2))).map
  (fun t => VG.Arm.Taint.pub t .r0) == some true
#guard (VG.Arm.Taint.step (VG.Arm.Taint.ofRegs [.r1]) (.dp .bic .r0 .r1 (.reg .r2))).map
  (fun t => VG.Arm.Taint.pub t .r0) == some false

end VG.Test.ArmLogical
