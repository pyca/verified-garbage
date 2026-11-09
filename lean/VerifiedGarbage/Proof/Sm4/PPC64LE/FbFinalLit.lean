module

public import VerifiedGarbage.Impl.Sm4.PPC64LE.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesLit
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! # SM4's final CFB and OFB functions on PPC64LE, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.Sm4.PPC64LE.cfbEncryptFinal
materialize_code Impl.Sm4.PPC64LE.cfbDecryptFinal
materialize_code Impl.Sm4.PPC64LE.ofbFinal

end VG
