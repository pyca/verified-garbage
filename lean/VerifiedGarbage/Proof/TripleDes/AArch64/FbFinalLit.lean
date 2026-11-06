module

public import VerifiedGarbage.Impl.TripleDes.AArch64.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.TripleDes.AArch64.FbLit
meta import VerifiedGarbage.Impl.TripleDes.AArch64.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FbLit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # Triple DES-CFB64's final functions' AArch64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.AArch64.cfbEncryptFinal
materialize_code Impl.TripleDes.AArch64.cfbDecryptFinal

end VG
