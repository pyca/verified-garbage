module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Gcm.X86_64.Stitch
meta import VerifiedGarbage.Impl.Gcm.X86_64.Stitch
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchR
meta import VerifiedGarbage.Impl.Gcm.X86_64.StitchR
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchTo
meta import VerifiedGarbage.Impl.Gcm.X86_64.StitchTo

/-! # The interleaved loops on 256-bit registers, as literals

For the checks of every instruction and the constant-time analyses of the
`VaesVpclmul` variant of AES-GCM on x86-64. -/

@[expose] public section

namespace VG

materialize_code Impl.Gcm.X86_64.Stitch.enc
materialize_code Impl.Gcm.X86_64.Stitch.dec
materialize_code Impl.Gcm.X86_64.StitchR.enc
materialize_code Impl.Gcm.X86_64.StitchR.decR
materialize_code Impl.Gcm.X86_64.StitchTo.enc
materialize_code Impl.Gcm.X86_64.StitchR.encTo
materialize_code Impl.Gcm.X86_64.StitchR.encN

end VG
