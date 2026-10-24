module

import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Modes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.Modes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! # SM4's modes on PPC64LE, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.Sm4.PPC64LE.cbcEncryptChained
materialize_code Impl.Sm4.PPC64LE.cbcDecryptChained
materialize_code Impl.Sm4.PPC64LE.ofb
materialize_code Impl.Sm4.PPC64LE.cfbEncrypt
materialize_code Impl.Sm4.PPC64LE.cfbDecrypt

end VG
