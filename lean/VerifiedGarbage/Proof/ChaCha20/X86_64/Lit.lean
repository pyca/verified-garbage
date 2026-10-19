module

public import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

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
