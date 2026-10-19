module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit
public import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512Split
meta import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512Split
import VerifiedGarbage.Impl.Aes.X86_64.Callee
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Impl.Aes.X86_64.Callee
meta import VerifiedGarbage.Impl.Gcm.X86_64
meta import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-!
# ChaCha20 with the data's first bytes from another buffer on x86-64 with AVX-512: the code as a literal
-/

@[expose] public section

namespace VG

materialize_code Impl.ChaCha20.X86_64.Avx512.xorSplit

end VG
