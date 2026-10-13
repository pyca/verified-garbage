module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Poly1305.X86_64
meta import VerifiedGarbage.Impl.Poly1305.X86_64
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Poly1305 on X86_64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Poly1305.X86_64.init
materialize_code Impl.Poly1305.X86_64.blocks
materialize_code Impl.Poly1305.X86_64.updatePre
materialize_code Impl.Poly1305.X86_64.updatePost
materialize_code Impl.Poly1305.X86_64.finalize

end VG
