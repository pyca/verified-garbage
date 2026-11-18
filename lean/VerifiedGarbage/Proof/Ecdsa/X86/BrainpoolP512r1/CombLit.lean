module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86Comb
public import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP512r1
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86Comb
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # ECDSA over brainpoolP512r1 on x86 (32-bit), with the comb: the code as a literal -/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.X86.signBrainpoolP512r1Comb

end VG
