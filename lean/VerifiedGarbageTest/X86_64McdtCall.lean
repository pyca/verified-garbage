module

import VerifiedGarbage.Impl.Mcdt.X86_64
import VerifiedGarbage.TCB.X86_64.Print
meta import VerifiedGarbage.Impl.Mcdt.X86_64
meta import VerifiedGarbage.TCB.X86_64.Print

/-! Tests of `Impl.Mcdt.X86_64.mcdtCall`: its text, which is Intel's MXCSR prologue and epilogue
that `ci/check_mcdt.py` accepts, and a run of its frame and blocks around a callee that leaves
MXCSR's status flags set, `rax` its result and `rbx` as it found it. -/
namespace VG.Test.X86_64McdtCall
open X86_64 Impl.Mcdt.X86_64

-- Intel's sequence, exactly: `stmxcsr`, then `mov r32, 8127`, its store and `ldmxcsr` of it,
-- and `lfence`; after the call, `lfence`, a `mov`, and `ldmxcsr` of the slot `stmxcsr` wrote.
#guard pro.flatMap Instr.asm == ["stmxcsr DWORD PTR [rsp]", "mov ebx, DWORD PTR [rsp]", "and ebx, 65535",
  "mov eax, 8127", "mov DWORD PTR [rsp+4], eax", "ldmxcsr DWORD PTR [rsp+4]", "lfence"]
#guard epi.flatMap Instr.asm == ["lfence", "mov DWORD PTR [rsp], ebx", "ldmxcsr DWORD PTR [rsp]"]
#guard Instr.asm (.push [.rbx, .rbx]) == ["push rbx", "push rbx"]
#guard Instr.asm (.pop .rbx 2) == ["pop rbx", "pop rbx"]

/-- The caller: `rbx` its own, MXCSR with a control bit cleared (`0x1F00`, no precision mask)
and a status flag set (`0x01`). -/
private def initial : State where
  gpr r := if r = .rsp then 0x1000 else if r = .rbx then 0x1122334455667788 else 42
  cf := some true
  zf := some false
  sf := none
  of := some false
  mxcsr := 0x1F01
  mem _ := 0
  rd := []
  wr := []

/-- The frame's push, then the prologue. -/
private def entered : Option State :=
  (isa.push (.push [.rbx, .rbx]) initial).bind (fun s => (execBlock isa pro s).map Prod.fst)

-- MXCSR is `0x1FBF` for the callee, `rbx` holds the caller's MXCSR, and the frame's first push
-- the caller's `rbx`.
#guard (entered.map fun s => (s.mxcsr, s.gpr .rbx, s.gpr .rax, s.gpr .rsp, s.mem.readW 0xff8 64)) ==
  some (0x1FBF, 0x1F01, 8127, 0xff0, 0x1122334455667788)

/-- A callee that returns 7 in `rax`, sets every status flag, and keeps `rbx`. -/
private def called (s : State) : State := { s.setReg .rax 7 with mxcsr := s.mxcsr ||| 0x3F }

/-- The epilogue and the frame's pop, after the callee. -/
private def returned : Option State :=
  entered.bind fun s₁ => ((execBlock isa epi (called s₁)).map Prod.fst).bind fun s₂ => isa.pop (.pop .rbx 2) s₁ s₂

-- The caller's MXCSR, `rbx` and `rsp`, and the callee's result.
#guard (returned.map fun s => (s.mxcsr, s.gpr .rbx, s.gpr .rax, s.gpr .rsp, s.wr)) ==
  some (0x1F01, 0x1122334455667788, 7, 0x1000, [])

end VG.Test.X86_64McdtCall
