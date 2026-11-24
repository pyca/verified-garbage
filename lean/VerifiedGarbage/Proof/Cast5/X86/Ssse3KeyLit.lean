module

public import VerifiedGarbage.Impl.Cast5.X86.Ssse3Key
import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Cast5.X86.Ssse3Key
meta import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# CAST5's key expansion by `pshufb` on x86 (32-bit): the code as literals

The look-ups' function (`Impl.Cast5.X86.Ssse3.Key.lookup`) and key expansion
over it as literals, which the checks of the whole function (`taint_decide`,
`lit_decide`) read rather than build the code again; the table in the
code's loads is the table's literal (`Ssse3Lit.lean`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86.Ssse3.Key

materialize_code Impl.Cast5.X86.Ssse3.Key.lookup
materialize_code Impl.Cast5.X86.Ssse3.Key.expandKey

end VG.Proof.Cast5.X86.Ssse3.Key
