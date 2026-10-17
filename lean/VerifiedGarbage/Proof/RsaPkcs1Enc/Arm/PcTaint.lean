module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Precomputed
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Precomputed
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # RSAES-PKCS1-v1_5 encryption with a precomputed public key on ARMv7: the pieces the taint analysis checks -/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Pc

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Precomputed

theorem head_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0]) (.block head) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem psBody_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .lr]) (.block psBody) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem sep_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0]) (.block sep) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.lr]) (.block [.cmp .lr (.imm 0)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem fin_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block [.mov .r0 (.reg .r3)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.RsaPkcs1Enc.Arm.Pc
