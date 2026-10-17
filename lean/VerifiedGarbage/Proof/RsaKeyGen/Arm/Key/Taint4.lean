module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint0
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint0
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # An RSA key on ARMv7: the stores the taint analysis checks -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key

/-- A store, with the working space's registers and the output's pointer and length public. -/
abbrev SCert (j : Nat) : Prop := ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r7, .r8, .r9, .r10, .r11])
    (VG.Impl.Rsa.Arm.CrtValues.store j) hc).isSome = true

theorem storeN_taint : SCert aN := ⟨_, by taint_decide⟩
theorem storeD_taint : SCert aD := ⟨_, by taint_decide⟩
theorem storeP_taint : SCert aP := ⟨_, by taint_decide⟩
theorem storeQ_taint : SCert aQ := ⟨_, by taint_decide⟩
theorem storeDp_taint : SCert aDP := ⟨_, by taint_decide⟩
theorem storeDq_taint : SCert aDQ := ⟨_, by taint_decide⟩
theorem storeQi_taint : SCert aQi := ⟨_, by taint_decide⟩
theorem retMask_taint : Cert (.block [.ldr .r0 .r8 sMask]) := ⟨_, by taint_decide⟩
theorem ret2_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block [.mov .r0 (.imm 2)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.RsaKeyGen.Arm.Key
