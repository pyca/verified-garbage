module

public import VerifiedGarbage.Impl.Idea.X86.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Idea.X86.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # IDEA-CFB64's final functions' x86 (32-bit) code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG.Proof.Idea.X86

materialize_flat_code cfbEncryptFinalCode := Impl.Idea.X86.cfbEncryptFinal
materialize_flat_code cfbDecryptFinalCode := Impl.Idea.X86.cfbDecryptFinal

end VG.Proof.Idea.X86
