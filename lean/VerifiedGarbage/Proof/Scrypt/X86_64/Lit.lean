module

public import VerifiedGarbage.Impl.Scrypt.X86_64.RoMixDirect
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Scrypt.X86_64.RoMixDirect
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

/-!
# scrypt on X86_64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Scrypt.X86_64.salsa
materialize_code Impl.Scrypt.X86_64.blockMix
materialize_code Impl.Scrypt.X86_64.blockMixFused
materialize_code Impl.Scrypt.X86_64.roMix

materialize_code Impl.Scrypt.X86_64.roMixDirect

end VG
