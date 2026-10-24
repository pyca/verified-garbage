module

import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
public import VerifiedGarbage.Impl.Camellia.PPC64LE.Modes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
meta import VerifiedGarbage.Impl.Camellia.PPC64LE.Modes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! # Camellia's modes on PPC64LE, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.Camellia.PPC64LE.cbcEncryptChained
materialize_code Impl.Camellia.PPC64LE.cbcDecryptChained
materialize_code Impl.Camellia.PPC64LE.ofb
materialize_code Impl.Camellia.PPC64LE.cfbEncrypt
materialize_code Impl.Camellia.PPC64LE.cfbDecrypt
materialize_code Impl.Camellia.PPC64LE.ctr

end VG
