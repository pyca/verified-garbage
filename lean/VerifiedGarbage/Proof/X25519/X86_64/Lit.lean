module

public import VerifiedGarbage.Impl.X25519.X86_64
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.X25519.X86_64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.TCB.X86_64.Target

/-!
# X25519 on x86-64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, `spSafe`,
properties of every instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead.
-/

@[expose] public section

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
