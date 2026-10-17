module

public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Impl.CmacTripleDes.Arm
meta import VerifiedGarbage.Impl.CmacTripleDes.Arm
import VerifiedGarbage.Proof.CmacTripleDes.Arm.KeysLit
meta import VerifiedGarbage.Proof.CmacTripleDes.Arm.KeysLit
import VerifiedGarbage.Proof.CmacTripleDes.Arm.RoundLit
meta import VerifiedGarbage.Proof.CmacTripleDes.Arm.RoundLit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-! # TDEA-CMAC's ARMv7 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.CmacTripleDes.Arm.init
materialize_code Impl.CmacTripleDes.Arm.update
materialize_code Impl.CmacTripleDes.Arm.finalize

end VG
