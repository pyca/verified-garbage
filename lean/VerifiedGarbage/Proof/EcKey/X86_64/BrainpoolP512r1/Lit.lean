module

public import VerifiedGarbage.Impl.EcKey.BrainpoolP512r1.X86_64
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.EcKey.BrainpoolP512r1.X86_64
import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP512r1Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP512r1Literals
import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.X86_64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.X86_64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

@[expose] public section

namespace VG.Proof.EcKey.X86_64.BrainpoolP512r1

open VG.Impl.EcKey.X86_64

materialize_code publicKeyBrainpoolP512r1

end VG.Proof.EcKey.X86_64.BrainpoolP512r1
