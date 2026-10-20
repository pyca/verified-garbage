module

public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Bignum.Arm.MaskBytes
public import VerifiedGarbage.Impl.Bignum.Arm.ModulusCheck
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Impl.Rsa.Arm.Recover
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Impl.Rsa.Arm.Recover
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-! # `vg_rsa_recover_primes` on ARMv7: the pieces of the failure and the entry the taint analysis checks -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover

theorem movR2_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r0, .lr])
    (.block [.mov .r2 (.imm 0)]) hc).isSome = true := ⟨_, by taint_decide⟩

theorem mask_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r0, .lr])
    VG.Impl.Bignum.Arm.maskBytes hc).isSome = true := ⟨_, by taint_decide⟩

theorem ret0_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [])
    (.block [.mov .r0 (.imm 0)]) hc).isSome = true := ⟨_, by taint_decide⟩

theorem check_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r4, .r6])
    (.block VG.Impl.Bignum.Arm.modulusCheck) hc).isSome = true := ⟨_, by taint_decide⟩

end VG.Proof.Rsa.Arm.Recover
