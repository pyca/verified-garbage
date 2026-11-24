module

public import VerifiedGarbage.Impl.Rc4.X86.Ssse3
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Rc4.X86.Ssse3
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# RC4 with the table's rows in XMM registers on x86 (32-bit): the code as literals

The two functions (`Impl/Rc4/X86/Ssse3.lean`) and the stream function's code
after its entry as literals (`materialize_code`), which the checks of the
whole functions (`taint_decide`, `lit_decide`) read rather than build the
code again.
-/

@[expose] public section

namespace VG

materialize_code Impl.Rc4.X86.Ssse3.init
materialize_code Impl.Rc4.X86.Ssse3.applyRest
materialize_code Impl.Rc4.X86.Ssse3.apply

end VG
