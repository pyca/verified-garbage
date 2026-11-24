module

public import VerifiedGarbage.Impl.Camellia.X86.Sse
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Camellia.X86.Sse
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Camellia on x86 (32-bit) in XMM registers: the code as literals

The code of the modes over the core that enciphers sixteen blocks at a time,
as literals (`materialize_flat_code`), which the checks of the whole
functions (`taint_decide`, `lit_decide`) read rather than build the code
again.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.Sse

materialize_flat_code cbcEncryptChainedCode := Impl.Camellia.X86.Sse.cbcEncryptChained
materialize_flat_code ofbCode := Impl.Camellia.X86.Sse.ofb
materialize_flat_code cfbEncryptCode := Impl.Camellia.X86.Sse.cfbEncrypt
materialize_flat_code cfbEncryptFinalCode := Impl.Camellia.X86.Sse.cfbEncryptFinal
materialize_flat_code cfbDecryptFinalCode := Impl.Camellia.X86.Sse.cfbDecryptFinal
materialize_flat_code ofbFinalCode := Impl.Camellia.X86.Sse.ofbFinal
materialize_flat_code cbcDecryptChainedCode := Impl.Camellia.X86.Sse.cbcDecryptChained
materialize_flat_code cfbDecryptCode := Impl.Camellia.X86.Sse.cfbDecrypt
materialize_flat_code ctrCode := Impl.Camellia.X86.Sse.ctr
materialize_flat_code ecbEncryptCode := Impl.Camellia.X86.Sse.ecb .encrypt
materialize_flat_code ecbDecryptCode := Impl.Camellia.X86.Sse.ecb .decrypt

end VG.Proof.Camellia.X86.Sse
