module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor
meta import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor
public import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx2
meta import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx2
public import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512
meta import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ChaCha20 on X86_64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.ChaCha20.X86_64.block
materialize_code Impl.ChaCha20.X86_64.Xor.xor
materialize_code Impl.ChaCha20.X86_64.Avx2.xor
materialize_code Impl.ChaCha20.X86_64.Avx512.xor

end VG
