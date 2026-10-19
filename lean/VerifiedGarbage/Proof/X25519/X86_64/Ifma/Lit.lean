module

public import VerifiedGarbage.Impl.X25519.X86_64.Ifma
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.X25519.X86_64.Ifma
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-!
# X25519 on x86-64 with AVX512_IFMA: the code as a literal

As for `vg_x25519` (`Proof/X25519/X86_64/Lit.lean`): the literal of the
unrolled code, checked once here, for the checks that evaluate it.
-/

@[expose] public section

namespace VG

materialize_code Impl.X25519.X86_64.x25519Ifma

end VG
