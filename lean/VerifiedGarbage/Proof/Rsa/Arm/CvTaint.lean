module

public import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # `vg_rsa_crt_values` on ARMv7: the pieces the taint analysis checks

Between the divisions (whose constant time is `Div.code_ct`) and around the
branch on the modulus' validity, every piece of `vg_rsa_crt_values` reads its
addresses and loop counts from the stack arguments (`argTaint _ 48`) and from
the registers given here, which the two runs agree on by correctness.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues

theorem entry_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 48) (.block entry) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem loads_taint : ∃ hc, (VG.Taint.check taint (argTaint [] 48) loads hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem divN_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r7, .r8, .r9] 48) (seqs divN) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem checks_taint : ∃ hc, (VG.Taint.check taint (argTaint [] 48) checks hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem divQ_taint : ∃ hc, (VG.Taint.check taint (argTaint [] 48) divQ hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem glue_taint : ∃ hc, (VG.Taint.check taint (argTaint [] 48)
    (.block (ctx ++ ([.ldr .r10 .r8 sDp, .ldr .r12 .r8 sDq] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem stores_taint :
    ∃ hc, (VG.Taint.check taint (argTaint [.r7, .r8, .r9, .r10, .r12] 48) stores hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem fail_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r3] 48) fail hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore_taint : ∃ hc, (VG.Taint.check taint (argTaint [] 48) (.block restore) hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.Rsa.Arm.CrtValues
