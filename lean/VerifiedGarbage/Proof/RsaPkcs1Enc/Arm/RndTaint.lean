module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Random
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Random
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # RSAES-PKCS1-v1_5 encryption from a random tape on ARMv7: the pieces the taint analysis checks -/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Rnd

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Random

theorem cmp8_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8]) (.block [.cmp .r8 (.imm 0)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem load_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r1, .r4]) (.block load) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem keep_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r5]) (.block keep) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp53_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5, .r3]) (.block [.cmp .r5 (.reg .r3)]) hc).isSome =
      true :=
  ⟨_, by taint_decide⟩

theorem cmp55_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5]) (.block [.cmp .r5 (.reg .r5)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp48_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r8]) (.block [.cmp .r4 (.reg .r8)]) hc).isSome =
      true :=
  ⟨_, by taint_decide⟩

theorem cmp50_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5]) (.block [.cmp .r5 (.imm 0)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tapeStore_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r7, .r4]) (.block tapeStore) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem status_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block status) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem fin_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block [.mov .r0 (.reg .r4)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem budget_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r3, .r8]) (.block budget) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem exhausted_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r7, .r8]) (.block exhausted) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem request_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r3, .r5, .r6, .r7, .r8]) (.block request) hc).isSome =
      true :=
  ⟨_, by taint_decide⟩

end VG.Proof.RsaPkcs1Enc.Arm.Rnd
