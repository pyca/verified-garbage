module

import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Modes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.Modes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! # Triple DES's modes on PPC64LE, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.PPC64LE.cbcEncryptChained
materialize_code Impl.TripleDes.PPC64LE.cbcDecryptChained
materialize_code Impl.TripleDes.PPC64LE.ofb
materialize_code Impl.TripleDes.PPC64LE.cfbEncrypt
materialize_code Impl.TripleDes.PPC64LE.cfbDecrypt
materialize_code Impl.TripleDes.PPC64LE.cfb8Encrypt
materialize_code Impl.TripleDes.PPC64LE.cfb8Decrypt

end VG
