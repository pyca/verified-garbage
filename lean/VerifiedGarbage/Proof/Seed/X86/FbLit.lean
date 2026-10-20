module

public import VerifiedGarbage.Impl.Seed.X86.Modes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Seed.X86.Modes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# SEED-OFB and SEED-CFB128 on x86 (32-bit): the code as literals

The code of OFB and CFB128 as literals (`materialize_code`), which the
checks of the whole functions (`taint_decide`, `lit_decide`) read rather
than build the code again.
Not flattened (`materialize_flat_code`): its unfolding measured slower here.
-/

@[expose] public section

namespace VG.Proof.Seed.X86

materialize_code ofbCode := Impl.Seed.X86.ofb
materialize_code cfbEncryptCode := Impl.Seed.X86.cfbEncrypt
materialize_code cfbDecryptCode := Impl.Seed.X86.cfbDecrypt

end VG.Proof.Seed.X86
