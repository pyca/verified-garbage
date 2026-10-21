module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint

/-! P-256 verification's precondition and public relation with its own table of `[m]G`,
`m = 1 … 256`, at `VG_P256_GTAB` (`P256Joint.p256v`), in place of the comb's. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64

/-- `VPre p256` with the verifier's table. -/
abbrev VPreG := VPreT p256 P256Joint.p256v.tsym P256Joint.p256v.combWords

/-- `JacPublic p256` with the verifier's table. -/
abbrev JacPublicG := JacPublicT p256 P256Joint.p256v.tsym

end VG.Proof.Ecdsa.Verify.AArch64
