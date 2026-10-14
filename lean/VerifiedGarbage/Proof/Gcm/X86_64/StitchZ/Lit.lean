module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZHTo
meta import VerifiedGarbage.Impl.Gcm.X86_64.StitchZHTo
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZP
meta import VerifiedGarbage.Impl.Gcm.X86_64.StitchZP
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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
