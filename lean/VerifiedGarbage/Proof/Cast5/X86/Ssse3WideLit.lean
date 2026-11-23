module

public import VerifiedGarbage.Impl.Cast5.X86.Ssse3Wide
import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Cast5.X86.Ssse3Wide
meta import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# CAST5's functions over sixteen blocks by `pshufb` on x86 (32-bit): the code as literals

The sixteen-block function (`Impl.Cast5.X86.Ssse3.Wide.cryptBlocks`) and
the functions over it as literals, which the checks of the whole functions
(`taint_decide`, `lit_decide`) read rather than build the code again. The
table in the code's loads is the table's literal (`Ssse3Lit.lean`), which
the kernel would otherwise evaluate from the S-boxes for each function.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86.Ssse3.Wide

materialize_code Impl.Cast5.X86.Ssse3.Wide.cryptBlocks
materialize_code Impl.Cast5.X86.Ssse3.Wide.cbcDecryptChained
materialize_code Impl.Cast5.X86.Ssse3.Wide.cfbDecrypt
materialize_code ecbEncryptCode := Impl.Cast5.X86.Ssse3.Wide.ecb true
materialize_code ecbDecryptCode := Impl.Cast5.X86.Ssse3.Wide.ecb false

end VG.Proof.Cast5.X86.Ssse3.Wide
