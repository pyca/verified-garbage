import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Seed.Arm.ExpandKey

/-!
# SEED on Arm: the code as literals

The code of the key expansion and of ECB in both directions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), which the checks of the whole functions
(`taint_decide`, `lit_decide`) read rather than build the code again in
each of them.
-/

namespace VG.Proof.Seed.Arm

materialize_flat_code expandKeyCode := Impl.Seed.Arm.expandKey
materialize_flat_code ecbEncrypt := Impl.Seed.Arm.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Seed.Arm.ecb .decrypt

end VG.Proof.Seed.Arm
