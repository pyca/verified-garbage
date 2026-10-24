module

public import VerifiedGarbage.Impl.Cast5.PPC64LE.Modes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Cast5.PPC64LE.Modes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! # CAST5's modes on PPC64LE, evaluated once -/

@[expose] public section

namespace VG.Impl.Cast5.PPC64LE
materialize_code cbcEncryptChained
materialize_code cbcDecryptChained
materialize_code ofb
materialize_code cfbEncrypt
materialize_code cfbDecrypt
end VG.Impl.Cast5.PPC64LE
