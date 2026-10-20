module

public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.X86_64
public import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP512r1Literals
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.X86_64
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP512r1Literals
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

@[expose] public section

namespace VG.Proof.Ecdh.X86_64.BrainpoolP512r1

open VG.Impl.Ecdh.X86_64

materialize_code exchangeBrainpoolP512r1

end VG.Proof.Ecdh.X86_64.BrainpoolP512r1
