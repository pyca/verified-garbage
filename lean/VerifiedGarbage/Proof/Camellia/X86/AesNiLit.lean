module

public import VerifiedGarbage.Impl.Camellia.X86.AesNiModes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Camellia.X86.AesNiModes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Camellia's chained modes by the AES S-box on x86 (32-bit): the code as literals

The code of the chained modes over the core that enciphers one block at a
time, as literals (`materialize_flat_code`), which the checks of the whole
functions (`taint_decide`, `lit_decide`) read rather than build the code
again.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.AesNi

materialize_flat_code cbcEncryptChainedCode := Impl.Camellia.X86.AesNi.cbcEncryptChained
materialize_flat_code ofbCode := Impl.Camellia.X86.AesNi.ofb
materialize_flat_code cfbEncryptCode := Impl.Camellia.X86.AesNi.cfbEncrypt
materialize_flat_code cfbEncryptFinalCode := Impl.Camellia.X86.AesNi.cfbEncryptFinal
materialize_flat_code cfbDecryptFinalCode := Impl.Camellia.X86.AesNi.cfbDecryptFinal
materialize_flat_code ofbFinalCode := Impl.Camellia.X86.AesNi.ofbFinal

end VG.Proof.Camellia.X86.AesNi
