module

public import VerifiedGarbage.Impl.Camellia.X86.Modes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Camellia.X86.Modes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Camellia-OFB and Camellia-CFB128 on x86 (32-bit): the code as literals

The code of OFB and CFB128 as literals (`materialize_flat_code`), which the
checks of the whole functions (`taint_decide`, `lit_decide`) read rather
than build the code again.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

materialize_flat_code ofbCode := Impl.Camellia.X86.ofb
materialize_flat_code cfbEncryptCode := Impl.Camellia.X86.cfbEncrypt
materialize_flat_code cfbDecryptCode := Impl.Camellia.X86.cfbDecrypt

end VG.Proof.Camellia.X86
