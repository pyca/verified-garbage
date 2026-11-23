module

public import VerifiedGarbage.Impl.TripleDes.X86.Ssse3
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.TripleDes.X86.Ssse3
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Triple DES's modes with its S-boxes by `pshufb` on x86 (32-bit): the code as literals

The code of the functions over the core of one block
(`Impl.TripleDes.X86.Ssse3.core`) as literals (`materialize_code`), which
the checks of the whole functions (`taint_decide`, `lit_decide`) read rather
than build the code again.
-/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.X86.Ssse3.cbcEncryptChained

end VG
