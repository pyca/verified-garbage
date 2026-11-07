module

public import VerifiedGarbage.Impl.Idea.AArch64.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Idea.AArch64.ModesLit
meta import VerifiedGarbage.Impl.Idea.AArch64.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Idea.AArch64.ModesLit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # IDEA-CFB64's final functions' AArch64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.AArch64.cfbEncryptFinal
materialize_code Impl.Idea.AArch64.cfbDecryptFinal

end VG
