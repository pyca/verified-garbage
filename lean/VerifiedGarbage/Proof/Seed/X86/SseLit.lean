module

public import VerifiedGarbage.Impl.Seed.X86.Sse
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Seed.X86.Sse
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# SEED on x86 (32-bit) in XMM registers: the code as literals

The code of the modes over the core that enciphers sixteen blocks at a time,
as literals (`materialize_code`), which the checks of the whole
functions (`taint_decide`, `lit_decide`) read rather than build the code
again.
-/

@[expose] public section

namespace VG.Proof.Seed.X86.Sse

materialize_code cbcEncryptChainedCode := Impl.Seed.X86.Sse.cbcEncryptChained
materialize_code ofbCode := Impl.Seed.X86.Sse.ofb
materialize_code cfbEncryptCode := Impl.Seed.X86.Sse.cfbEncrypt
materialize_code cfbEncryptFinalCode := Impl.Seed.X86.Sse.cfbEncryptFinal
materialize_code cfbDecryptFinalCode := Impl.Seed.X86.Sse.cfbDecryptFinal
materialize_code ofbFinalCode := Impl.Seed.X86.Sse.ofbFinal
materialize_code cbcDecryptChainedCode := Impl.Seed.X86.Sse.cbcDecryptChained
materialize_code cfbDecryptCode := Impl.Seed.X86.Sse.cfbDecrypt
materialize_code ecbEncryptCode := Impl.Seed.X86.Sse.ecb .encrypt
materialize_code ecbDecryptCode := Impl.Seed.X86.Sse.ecb .decrypt

end VG.Proof.Seed.X86.Sse
