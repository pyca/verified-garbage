module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.X25519.X86.Verified
import VerifiedGarbage.Proof.X25519.X86.Lit
import VerifiedGarbage.Proof.X25519.X86.Base.Verified
import VerifiedGarbage.Proof.X25519.X86.Exchange
import VerifiedGarbage.Proof.X25519.X86.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Impl.X25519.X86.Base
import VerifiedGarbage.Proof.X25519.X86.Base.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # X25519 (RFC 7748) on x86 -/

namespace VG.Artifacts.X25519.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.X25519.exchangeApi.artifact X86.target {
    code := Impl.X25519.X86.Fn.exchange
    verified := Proof.X25519.X86.Scrub.exchange_scrubbed },
  Spec.X25519.x25519BaseApi.artifact X86.target {
    code := Impl.X25519.X86.Fn.base
    verified := Proof.X25519.X86.Scrub.base_scrubbed }]

spec_apis artifacts

end VG.Artifacts.X25519.X86
