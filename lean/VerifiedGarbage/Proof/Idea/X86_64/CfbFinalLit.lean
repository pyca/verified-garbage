module

public import VerifiedGarbage.Impl.Idea.X86_64.CfbFinal
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Idea.X86_64.Lit
meta import VerifiedGarbage.Impl.Idea.X86_64.CfbFinal
meta import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Idea.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # IDEA-CFB64's x86-64 final functions as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.X86_64.cfbEncryptFinal
materialize_code Impl.Idea.X86_64.cfbDecryptFinal

end VG
