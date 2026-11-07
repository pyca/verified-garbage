module

public import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.X86.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
meta import VerifiedGarbage.Impl.TripleDes.X86.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Triple DES-CFB64's final functions' x86 (32-bit) code as literals, for kernel-evaluated checks

They read the literals of the block function's parts (`FunctionsLit.lean`),
as `FbLit.lean` does.
-/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.X86.cfbEncryptFinal
materialize_code Impl.TripleDes.X86.cfbDecryptFinal

end VG
