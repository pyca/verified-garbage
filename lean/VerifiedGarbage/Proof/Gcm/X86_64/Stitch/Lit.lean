module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchR
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Gcm.X86_64.StitchR
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # The interleaved loops on 256-bit registers, as literals

For the checks of every instruction and the constant-time analyses of the
`VaesVpclmul` variant of AES-GCM on x86-64. -/

@[expose] public section

namespace VG

materialize_code Impl.Gcm.X86_64.Stitch.enc
materialize_code Impl.Gcm.X86_64.Stitch.dec
materialize_code Impl.Gcm.X86_64.StitchR.encR
materialize_code Impl.Gcm.X86_64.StitchR.decR
materialize_code Impl.Gcm.X86_64.StitchTo.enc
materialize_code Impl.Gcm.X86_64.StitchR.encToR
materialize_code Impl.Gcm.X86_64.StitchR.encN

end VG
