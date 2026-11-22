module

public import VerifiedGarbage.Impl.Seed.X86.AesNiWide
public import VerifiedGarbage.Impl.Seed.X86.AesNiWideEcb
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Seed.X86.AesNiWide
meta import VerifiedGarbage.Impl.Seed.X86.AesNiWideEcb
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# SEED's wide modes by the AES S-box on x86 (32-bit): the code as literals

The code of the modes over the core that enciphers four blocks at a time,
as literals (`materialize_flat_code`), which the checks of the whole
functions (`taint_decide`, `lit_decide`) read rather than build the code
again.
-/

@[expose] public section

namespace VG.Proof.Seed.X86.AesNiWide

materialize_flat_code cbcDecryptChainedCode := Impl.Seed.X86.AesNiWide.cbcDecryptChained
materialize_flat_code cfbDecryptCode := Impl.Seed.X86.AesNiWide.cfbDecrypt
materialize_flat_code ecbEncryptCode := Impl.Seed.X86.AesNiWide.ecb .encrypt
materialize_flat_code ecbDecryptCode := Impl.Seed.X86.AesNiWide.ecb .decrypt

end VG.Proof.Seed.X86.AesNiWide
