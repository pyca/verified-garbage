module

import VerifiedGarbage.TCB.AArch64.Encode
meta import VerifiedGarbage.TCB.AArch64.Encode
import VerifiedGarbage.TCB.AArch64.Print
meta import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# Barriers: `dsb sy`, `isb` and `sb`

Their semantics (none on the model's state), their text, their machine code,
the feature they require and their taint. The words are GNU as 2.46's for
the printed text (`aarch64-linux-gnu-as -march=armv8.5-a`, then `objdump
-d`), which with `-march=armv8-a` refuses `sb` ("selected processor does not
support `sb'"); they match the fields of DDI 0602 2026-03, "DSB", "ISB" and
"SB".
-/

namespace VG.Test.AArch64Barrier

open AArch64

private def state (dit : Bool) : State where
  gpr r := if r = .x1 then 0x1234 else 0xffffffffffffffff
  sp := 0x1000
  mem _ := 0x5a
  rd := []
  wr := []
  dit := dit

private def all : List Barrier := [.dsbSy, .isb, .sb]

-- Each leaves the whole state as it is, PSTATE.DIT included, and accesses
-- no memory.
#guard [false, true].all fun d => all.all fun b =>
  (exec (.barrier b) (state d)).map (fun s =>
    (s.dit, s.gpr .x0, s.gpr .x1, s.sp, s.mem 0, s.nf, s.zf, s.c, s.vf)) ==
  some (d, 0xffffffffffffffff, 0x1234, 0x1000, 0x5a, false, false, false, false)
#guard all.all fun b => addrs (.barrier b) (state true) == []

#guard Instr.asm (.barrier .dsbSy) == ["dsb sy"]
#guard Instr.asm (.barrier .isb) == ["isb"]
#guard Instr.asm (.barrier .sb) == ["sb"]

#guard Instr.encode (.barrier .dsbSy) == some [0xD5033F9F]
#guard Instr.encode (.barrier .isb) == some [0xD5033FDF]
#guard Instr.encode (.barrier .sb) == some [0xD50330FF]

#guard isa.requires (.barrier .dsbSy) == []
#guard isa.requires (.barrier .isb) == []
#guard isa.requires (.barrier .sb) == ["sb"]

-- They change no register's taint.
#guard all.all fun b =>
  ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x1]) (.barrier b)).map
    (fun τ => (AArch64.Taint.pub τ .x0, AArch64.Taint.pub τ .x1))) == some (false, true)

end VG.Test.AArch64Barrier
