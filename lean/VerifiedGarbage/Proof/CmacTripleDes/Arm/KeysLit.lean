module

public import VerifiedGarbage.Impl.CmacTripleDes.Arm.Round
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.CmacTripleDes.Arm.Round
meta import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! # The key schedule's code as a literal, for kernel-evaluated checks

Evaluated once, here: the checks of `Keys.lean` and the literal of `init`
(`Lit.lean`), which runs it, read it. -/

@[expose] public section

namespace VG

materialize_value Impl.CmacTripleDes.Arm.roundKeys

theorem Proof.CmacTripleDes.Arm.roundKeys_eq :
    Impl.CmacTripleDes.Arm.roundKeys = Impl.CmacTripleDes.Arm.roundKeys.lit :=
  Impl.CmacTripleDes.Arm.roundKeys.lit_eq

end VG
