module

public import VerifiedGarbage.Impl.Cast5.X86.Ssse3
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Cast5.X86.Ssse3
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# CAST5 with its S-box look-ups by `pshufb` on x86 (32-bit): the table and the code as literals

The table of the planes of S1 to S4 and the constants
(`Impl.Cast5.X86.Ssse3.table`), the look-ups' function and the functions
over it as literals, which the checks of the whole functions
(`taint_decide`, `lit_decide`) read rather than build again.
-/

@[expose] public section

namespace VG

materialize_value Impl.Cast5.X86.Ssse3.table
materialize_code Impl.Cast5.X86.Ssse3.lookup
materialize_code Impl.Cast5.X86.Ssse3.cbcEncryptChained
materialize_code Impl.Cast5.X86.Ssse3.ofb
materialize_code Impl.Cast5.X86.Ssse3.cfbEncrypt
materialize_code Impl.Cast5.X86.Ssse3.cfbEncryptFinal
materialize_code Impl.Cast5.X86.Ssse3.cfbDecryptFinal
materialize_code Impl.Cast5.X86.Ssse3.ofbFinal

end VG
