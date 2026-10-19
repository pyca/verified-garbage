module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZHTo
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Gcm.X86_64.StitchZHTo
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

/-! # The interleaved loops on 512-bit registers, as literals

For the checks of every instruction and the constant-time analyses of the
`VaesVpclmulAvx512` variant of AES-GCM on x86-64. -/

@[expose] public section

namespace VG

materialize_code Impl.Gcm.X86_64.StitchZ.enc
materialize_code Impl.Gcm.X86_64.StitchZ.dec
materialize_code Impl.Gcm.X86_64.StitchZP.enc
materialize_code Impl.Gcm.X86_64.StitchZP.dec
materialize_code Impl.Gcm.X86_64.StitchZH.encR
materialize_code Impl.Gcm.X86_64.StitchZH.decR
materialize_code Impl.Gcm.X86_64.StitchZTo.enc
materialize_code Impl.Gcm.X86_64.StitchZTo.encP
materialize_code Impl.Gcm.X86_64.StitchZHTo.encR

end VG
