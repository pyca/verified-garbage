module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86_64
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86_64
import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP384r1Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP384r1Literals
import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.X86_64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.X86_64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.BrainpoolP384r1

open VG.Impl.Ecdsa.X86_64

materialize_code signBrainpoolP384r1

end VG.Proof.Ecdsa.X86_64.BrainpoolP384r1
