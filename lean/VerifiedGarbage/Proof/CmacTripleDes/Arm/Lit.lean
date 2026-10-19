module

public import VerifiedGarbage.Impl.CmacTripleDes.Arm
public import Batteries.Logic
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.CmacTripleDes.Arm
import VerifiedGarbage.Proof.CmacTripleDes.Arm.KeysLit
meta import VerifiedGarbage.Proof.CmacTripleDes.Arm.KeysLit
import VerifiedGarbage.Proof.CmacTripleDes.Arm.RoundLit
meta import VerifiedGarbage.Proof.CmacTripleDes.Arm.RoundLit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-! # TDEA-CMAC's ARMv7 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.CmacTripleDes.Arm.init
materialize_code Impl.CmacTripleDes.Arm.update
materialize_code Impl.CmacTripleDes.Arm.finalize

end VG
