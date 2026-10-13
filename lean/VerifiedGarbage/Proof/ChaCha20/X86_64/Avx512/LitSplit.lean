module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit
public import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512Split
meta import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512Split
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# ChaCha20 with the data's first bytes from another buffer on x86-64 with AVX-512: the code as a literal
-/

@[expose] public section

namespace VG

materialize_code Impl.ChaCha20.X86_64.Avx512.xorSplit

end VG
