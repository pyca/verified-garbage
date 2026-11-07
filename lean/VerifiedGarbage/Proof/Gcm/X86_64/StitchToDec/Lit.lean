module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchToDec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Gcm.X86_64.StitchToDec
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # The out-of-place decryption loop on 256-bit registers, as a literal

For the checks of every instruction and the constant-time analyses of the
`VaesVpclmul` and `VaesVpclmulAvx512` variants of AES-GCM on x86-64. -/

@[expose] public section

namespace VG

materialize_code Impl.Gcm.X86_64.StitchToDec.decToR

end VG
