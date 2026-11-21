module

public import VerifiedGarbage.Proof.X448.X86.Verified
public import VerifiedGarbage.Proof.X448.X86.Base
public import VerifiedGarbage.Proof.Ed448.CombFacts
import VerifiedGarbage.Proof.X448.X86.Lit
public import VerifiedGarbage.Proof.X448.X86.Exchange
public import VerifiedGarbage.Proof.X448.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.X448.X86.Base
public import VerifiedGarbage.TCB.X86.Print

/-! # X448 (RFC 7748) on x86 -/

@[expose] public section

namespace VG.Artifacts.X448.X86

def artifacts : List Artifact := [
  Spec.X448.exchangeApi.artifact X86.target {
    code := Impl.X448.X86.Fn.exchange
    verified := Proof.X448.X86.Scrub.exchange_scrubbed },
  Spec.X448.x448BaseApi.artifact X86.target {
    code := Impl.X448.X86.Fn.base
    verified := Proof.X448.X86.Scrub.base_scrubbed }]

end VG.Artifacts.X448.X86
