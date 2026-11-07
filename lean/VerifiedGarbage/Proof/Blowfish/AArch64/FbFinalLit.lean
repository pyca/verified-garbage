module

public import VerifiedGarbage.Impl.Blowfish.AArch64.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Blowfish.AArch64.ModesLit
meta import VerifiedGarbage.Impl.Blowfish.AArch64.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Blowfish.AArch64.ModesLit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # Blowfish-CFB64's final functions' AArch64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.Blowfish.AArch64.cfbEncryptFinal
materialize_code Impl.Blowfish.AArch64.cfbDecryptFinal

end VG
