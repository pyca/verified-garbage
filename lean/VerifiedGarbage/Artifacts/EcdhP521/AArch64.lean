module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P521
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.P521.AArch64.Law
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeVerified

/-! # ECDH over P-521 on AArch64 -/

@[expose] public section
namespace VG.Artifacts.EcdhP521.AArch64
open VG.Proof.P521.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P521.exchangeApi.artifact AArch64.target {
    code := Impl.Weierstrass.AArch64.P521Native.exchange
    stack := 3456
    verified := Proof.Weierstrass.AArch64.P521Native.native_verified hasLaw.law hasLaw.inv hasLaw.prime }]

end VG.Artifacts.EcdhP521.AArch64
