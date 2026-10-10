import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.X25519.X86

/-!
# X25519 on x86 (32-bit): the code as a literal

The field arithmetic is fully unrolled (about 23,000 instructions in all): the
literal of the code (`materialize_code`, `Proof/Framework/Lit.lean`) spares
the kernel building the instructions again in every check that evaluates the
code (constant time, `spSafe`).
-/

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
