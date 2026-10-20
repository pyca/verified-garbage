module

public import VerifiedGarbage.Impl.Scrypt.X86_64.RoMixDirect
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Scrypt.X86_64.RoMixDirect
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

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
