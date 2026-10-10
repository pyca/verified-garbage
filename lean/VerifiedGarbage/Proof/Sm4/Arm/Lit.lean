import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Sm4.Arm.Ecb
import VerifiedGarbage.Impl.Sm4.Arm.ExpandKey

/-!
# SM4 on Arm: the code as literals

The code of the key expansion and of ECB in both directions as literals
(`materialize_code`, `Proof/Framework/Lit.lean`), which the checks of the
whole functions (`taint_decide`, `lit_decide`) read rather than build the
code again in each of them.
-/

namespace VG.Proof.Sm4.Arm

materialize_flat_code expandKeyCode := Impl.Sm4.Arm.expandKey
materialize_flat_code ecbEncrypt := Impl.Sm4.Arm.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Sm4.Arm.ecb .decrypt

end VG.Proof.Sm4.Arm
