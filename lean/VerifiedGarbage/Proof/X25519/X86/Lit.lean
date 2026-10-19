module

public import VerifiedGarbage.Impl.X25519.X86.Fn
meta import VerifiedGarbage.Impl.X25519.X86.Fn
public import VerifiedGarbage.Proof.X25519.X86.Field32.Lit
meta import VerifiedGarbage.Proof.X25519.X86.Field32.Lit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

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
