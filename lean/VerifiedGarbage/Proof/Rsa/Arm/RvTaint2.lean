module

public import VerifiedGarbage.Impl.Rsa.Arm.Recover
meta import VerifiedGarbage.Impl.Rsa.Arm.Recover
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: the pieces of Montgomery multiplication's setup the taint analysis checks -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover

/-- The registers of the working space's context. -/
abbrev ctxRegs : List Reg := [.r7, .r8, .r9]

theorem zeroZ_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (sub3 aZ aN aN) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem oneZ_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (copy aOne aZ) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `montSet` before the stack. -/
abbrev montHead : List Instr := setOne aOne ++ (ptr .r0 mBase ++ [.dp .sub .r0 .r0 (.imm 256)])

/-- `montSet` from the stack on. -/
abbrev montStack : List Instr :=
  [.addSp .r12 0, .str .r0 .r12 0, .ldrSp .r7 aoK, .dp .add .r7 .r7 (.imm 7), .mov .r7 (.shifted .r7 .lsr 3),
    .mov .r3 (.imm 0)]

theorem montSet_eq : setOne aOne ++ montSet = montHead ++ montStack := rfl

theorem montHead_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (.block montHead) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem clrTopR2_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (.block (clrTop mR2)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem xmOne_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (copy mXm aOne) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem oXm_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (copy aO mXm) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ngO_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (sub3 aNg aN aO) hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.Rsa.Arm.Recover
