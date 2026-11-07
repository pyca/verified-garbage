module

public import VerifiedGarbage.Impl.Idea.X86_64.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
meta import VerifiedGarbage.Impl.Idea.X86_64.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # IDEA-CFB64's and IDEA-OFB's final functions' x86-64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.X86_64.cfbEncryptFinal
materialize_code Impl.Idea.X86_64.cfbDecryptFinal
materialize_code Impl.Idea.X86_64.ofbFinal

end VG
