module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Precomputed
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Precomputed
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # RSASSA-PKCS1-v1_5 verification with a precomputed public key on ARMv7: the pieces the taint analysis checks -/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Vf

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Precomputed

theorem cmp_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0]) (.block [.cmp .r0 (.imm 0)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ret0_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block ret0) hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.RsaPkcs1Sig.Arm.Vf
