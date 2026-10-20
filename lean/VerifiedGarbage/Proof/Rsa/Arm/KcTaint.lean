module

public import VerifiedGarbage.Impl.Rsa.Arm.KeyCheck
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.KeyCheck
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The checks of an RSA key on ARMv7: the pieces the taint analysis checks

Between the divisions (whose constant time is `Div.code_ct`), every piece of
the checks computes its addresses and loop counts from the registers given
here, which two runs agree on by correctness: `r8` and `n_len` in `r11` at
the start, `r8` after a division, and `r7`–`r9` otherwise.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck

theorem start_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8, .r11]) start hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ctxDiv_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8]) (.block ctxDiv) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem crtChecks_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) crtChecks hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem dChecks1_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) dChecks1 hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem dChecks2_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) dChecks2 hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem dChecks3_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) dChecks3 hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.Rsa.Arm.KeyCheck

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck

theorem eLoad_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8]) (.block [.ldr .r1 .r8 sE, .ldr .lr .r8 sEl]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem eCmp_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs []) (.block [.cmp .r7 (.imm 1)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ret_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8]) (.block ret) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ret0_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs []) (.block ret0) hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.Rsa.Arm.KeyCheck
