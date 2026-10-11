import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.X25519.X86_64

/-!
# X25519 on x86-64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, `spSafe`,
properties of every instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead.
-/

namespace VG.Proof.X25519.X86_64.Lit
open VG.Impl.X25519.X86_64

/-! The field operations are templates (`materialize_template`), each
evaluated once with its offsets free rather than once for every product, sum
and swap of the code. -/

materialize_template mulT := mul
materialize_template sqrT := sqr
materialize_template a24T := Field.a24add baseline
materialize_template mul2T := Field.mul2 baseline
materialize_template sqr2T := Field.sqr2 baseline
materialize_template addT := add
materialize_template subT := sub
materialize_template cswapT := cswap

end VG.Proof.X25519.X86_64.Lit

namespace VG

materialize_code Impl.X25519.X86_64.invertFn
materialize_code Impl.X25519.X86_64.x25519

end VG
