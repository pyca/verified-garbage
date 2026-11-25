module

public import VerifiedGarbage.Impl.Ecdh.P521.AArch64
public import VerifiedGarbage.Proof.Ecdh.AArch64.P521.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.P521.AArch64.Law
public import VerifiedGarbage.Spec.Ecdh.P521
public import VerifiedGarbage.TCB.AArch64.Target

/-! # ECDH over P-521 (SP 800-56A) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcdhP521.AArch64

open VG.Proof.P521.AArch64 (hasLaw)

def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdh.P521.exchangeApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Fn.exchangeP521
    verified := Proof.Ecdh.AArch64.P521.exchange_scrubbed hasLaw.law hasLaw.inv hasLaw.prime }]

end VG.Artifacts.EcdhP521.AArch64
