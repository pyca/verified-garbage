module

public import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowers
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Termination and table contents for the checkpoint loop. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

variable {fld : Arith} [EdArith fld]

theorem powersInit_ok (s : State) :
    WP isa (.block [.mov32 .rbx (.imm 0)]) s fun t => t.gpr .rbx = 0 ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

end VG.Proof.Ed25519.X86_64
