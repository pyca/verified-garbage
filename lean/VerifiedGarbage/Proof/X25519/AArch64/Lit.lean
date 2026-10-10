import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.X25519.AArch64

/-!
# X25519 on AArch64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, properties of
every instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead. The field operations
are templates (`materialize_template`), each evaluated once with its offsets
free rather than once for every product, sum and swap of the code.
-/

namespace VG.Proof.X25519.AArch64.Lit
open VG.Impl.X25519.AArch64

materialize_template mulT := mul
materialize_template mulSmallT := mulSmall
materialize_template addT := add
materialize_template subT := sub
materialize_template cswapT := cswap
materialize_template copyT := copy

end VG.Proof.X25519.AArch64.Lit

namespace VG

materialize_code Impl.X25519.AArch64.x25519

end VG
