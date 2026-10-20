module

public import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.X86.Fb
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
meta import VerifiedGarbage.Impl.TripleDes.X86.Fb
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Triple DES-OFB, -CFB64 and -CFB8 on x86 (32-bit): the code as literals

The code of the functions as literals (`materialize_code`), which the checks
of the whole functions (`taint_decide`, `lit_decide`) read rather than build
the code again. They read the literals of the block function's parts
(`FunctionsLit.lean`), as `CbcLit.lean` does.
-/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.X86.ofb
materialize_code Impl.TripleDes.X86.cfbEncrypt
materialize_code Impl.TripleDes.X86.cfbDecrypt
materialize_code Impl.TripleDes.X86.cfb8Encrypt
materialize_code Impl.TripleDes.X86.cfb8Decrypt

end VG
