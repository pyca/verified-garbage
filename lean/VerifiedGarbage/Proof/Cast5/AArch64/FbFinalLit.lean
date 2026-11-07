module

public import VerifiedGarbage.Impl.Cast5.AArch64.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
meta import VerifiedGarbage.Impl.Cast5.AArch64.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # CAST5-CFB64's final functions' AArch64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.Cast5.AArch64.cfbEncryptFinal
materialize_code Impl.Cast5.AArch64.cfbDecryptFinal

end VG
