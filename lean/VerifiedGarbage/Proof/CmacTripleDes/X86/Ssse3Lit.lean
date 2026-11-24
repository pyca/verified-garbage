module

public import VerifiedGarbage.Impl.CmacTripleDes.X86.Ssse3
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.CmacTripleDes.X86.Ssse3
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Streaming TDEA-CMAC with Triple DES's S-boxes by `pshufb` on x86 (32-bit): the code as literals

The internal function that chains blocks and the two streaming functions
over it (`Impl/CmacTripleDes/X86/Ssse3.lean`) as literals
(`materialize_code`), which the checks of the whole functions
(`taint_decide`, `lit_decide`) read rather than build the code again.
-/

@[expose] public section

namespace VG

materialize_code Impl.CmacTripleDes.X86.Ssse3.chainRun
materialize_code Impl.CmacTripleDes.X86.Ssse3.chain
materialize_code Impl.CmacTripleDes.X86.Ssse3.absorb
materialize_code Impl.CmacTripleDes.X86.Ssse3.finish

end VG
