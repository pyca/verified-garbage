module

public import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# ChaCha20 on X86_64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.ChaCha20.X86_64.block
materialize_code Impl.ChaCha20.X86_64.Xor.xor
materialize_code Impl.ChaCha20.X86_64.Avx2.xor
materialize_code Impl.ChaCha20.X86_64.Avx2.xorVL
materialize_code Impl.ChaCha20.X86_64.Avx512.xor

end VG
