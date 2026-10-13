module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.X25519.X86_64.Ifma
meta import VerifiedGarbage.Impl.X25519.X86_64.Ifma
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# X25519 on x86-64 with AVX512_IFMA: the code as a literal

As for `vg_x25519` (`Proof/X25519/X86_64/Lit.lean`): the literal of the
unrolled code, checked once here, for the checks that evaluate it.
-/

@[expose] public section

namespace VG

materialize_code Impl.X25519.X86_64.x25519Ifma

end VG
