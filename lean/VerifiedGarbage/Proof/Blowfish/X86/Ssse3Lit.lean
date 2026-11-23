module

public import VerifiedGarbage.Impl.Blowfish.X86.Ssse3
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Blowfish.X86.Ssse3
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Blowfish with its S-box look-ups by `pshufb` on x86 (32-bit): the code as literals

The block function (`Impl.Blowfish.X86.Ssse3.encryptBlock`) and the
functions over it as literals (`materialize_code`), which the checks of the
whole functions (`taint_decide`, `lit_decide`) read rather than build the
code again.
-/

@[expose] public section

namespace VG

materialize_code Impl.Blowfish.X86.Ssse3.encryptBlock
materialize_code Impl.Blowfish.X86.Ssse3.cbcEncryptChained
materialize_code Impl.Blowfish.X86.Ssse3.ofb
materialize_code Impl.Blowfish.X86.Ssse3.cfbEncrypt
materialize_code Impl.Blowfish.X86.Ssse3.cfbDecrypt
materialize_code Impl.Blowfish.X86.Ssse3.cfbEncryptFinal
materialize_code Impl.Blowfish.X86.Ssse3.cfbDecryptFinal
materialize_code Impl.Blowfish.X86.Ssse3.ofbFinal

end VG
