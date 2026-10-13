module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.X25519.X86
meta import VerifiedGarbage.Impl.X25519.X86
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# X25519 on x86 (32-bit): the code as a literal

The field arithmetic is fully unrolled (about 23,000 instructions in all): the
literal of the code (`materialize_code`, `Proof/Framework/Lit.lean`) spares
the kernel building the instructions again in every check that evaluates the
code (constant time, `spSafe`).
-/

@[expose] public section

namespace VG.Impl.X25519.X86

materialize_template mulSqT := mulSq
materialize_template mulPrT := mulPr
materialize_template mulSmallT := mulSmall
materialize_template addT := add
materialize_template subT := sub
materialize_template copyT := copy
materialize_template cswapT := cswap

materialize_code x25519

end VG.Impl.X25519.X86
