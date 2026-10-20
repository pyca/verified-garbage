module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZHTo
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Gcm.X86_64.StitchZHTo
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

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
materialize_code Impl.Gcm.X86_64.StitchZHTo.encN

end VG
