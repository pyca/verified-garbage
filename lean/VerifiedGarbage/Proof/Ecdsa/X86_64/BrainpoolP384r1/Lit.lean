module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86_64
import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP384r1Literals
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86_64
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP384r1Literals
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.BrainpoolP384r1

open VG.Impl.Ecdsa.X86_64

materialize_code signBrainpoolP384r1

end VG.Proof.Ecdsa.X86_64.BrainpoolP384r1
