module

import VerifiedGarbage.Proof.Sm4.AArch64.Lit
meta import VerifiedGarbage.Proof.Sm4.AArch64.Lit
public import VerifiedGarbage.Impl.Sm4.AArch64.Fb
meta import VerifiedGarbage.Impl.Sm4.AArch64.Fb
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# SM4-OFB and SM4-CFB128 on AArch64: the code as literals

As `Lit.lean`, for the feedback modes.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64

materialize_flat_code ofbCode := Impl.Sm4.AArch64.ofb
materialize_flat_code cfbEncryptCode := Impl.Sm4.AArch64.cfbEncrypt
materialize_flat_code cfbDecryptCode := Impl.Sm4.AArch64.cfbDecrypt

end VG.Proof.Sm4.AArch64
