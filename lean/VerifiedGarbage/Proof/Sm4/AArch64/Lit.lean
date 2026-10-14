module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.Sm4.AArch64.Ecb
meta import VerifiedGarbage.Impl.Sm4.AArch64.Ecb
public import VerifiedGarbage.Impl.Sm4.AArch64.ExpandKey
meta import VerifiedGarbage.Impl.Sm4.AArch64.ExpandKey
import VerifiedGarbage.Impl.Sm4.AArch64.Ctr
meta import VerifiedGarbage.Impl.Sm4.AArch64.Ctr
public import VerifiedGarbage.Impl.Sm4.AArch64.Cbc
meta import VerifiedGarbage.Impl.Sm4.AArch64.Cbc
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# SM4 on AArch64: the code as literals

The code of the key expansion, of ECB in both directions, of CTR and of CBC
in both directions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), which the checks
of the whole functions (`taint_decide`, `lit_decide`) read rather than build
the code again.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64

materialize_flat_code expandKeyCode := Impl.Sm4.AArch64.expandKey
materialize_flat_code ecbEncrypt := Impl.Sm4.AArch64.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Sm4.AArch64.ecb .decrypt
materialize_flat_code ecbAnyCode := Impl.Sm4.AArch64.ecbAny
materialize_flat_code ctrCode := Impl.Sm4.AArch64.ctr
materialize_flat_code cbcEncryptCode := Impl.Sm4.AArch64.cbcEncrypt
materialize_flat_code cbcDecryptCode := Impl.Sm4.AArch64.cbcDecrypt

end VG.Proof.Sm4.AArch64
