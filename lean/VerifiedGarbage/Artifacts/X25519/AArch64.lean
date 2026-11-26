module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Impl.X25519.AArch64.Fn
import VerifiedGarbage.Proof.Ed25519.AArch64.DivstepSound
import VerifiedGarbage.Proof.X25519.AArch64.LadderVerified
import VerifiedGarbage.Proof.X25519.AArch64.Base.Verified
import VerifiedGarbage.Proof.X25519.AArch64.Base.Residue
import VerifiedGarbage.Proof.X25519.AArch64.Exchange
import VerifiedGarbage.Proof.X25519.AArch64.ExchangeResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # X25519 (RFC 7748) on AArch64 -/

namespace VG.Artifacts.X25519.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.X25519.exchangeApi.artifact AArch64.target {
    code := Impl.X25519.AArch64.Fn.exchange
    verified := Proof.X25519.AArch64.ExchangeResidue.exchangeCode_scrubbed },
  Spec.X25519.x25519BaseApi.artifact AArch64.target {
    written := [("scratch", 1024)]
    code := Impl.X25519.AArch64.Fn.x25519Base
    verified := Proof.X25519.AArch64.Base.x25519BaseCleared_scrubbed
    writtenOk := Proof.X25519.AArch64.Base.x25519BaseCleared_written }]

spec_apis artifacts

end VG.Artifacts.X25519.AArch64
