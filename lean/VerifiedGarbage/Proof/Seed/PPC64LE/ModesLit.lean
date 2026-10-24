module

public import VerifiedGarbage.Impl.Seed.PPC64LE.Modes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Seed.PPC64LE.Modes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! # SEED's modes on PPC64LE, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.Seed.PPC64LE.cbcEncryptChained
materialize_code Impl.Seed.PPC64LE.cbcDecryptChained
materialize_code Impl.Seed.PPC64LE.ofb
materialize_code Impl.Seed.PPC64LE.cfbEncrypt
materialize_code Impl.Seed.PPC64LE.cfbDecrypt

end VG
