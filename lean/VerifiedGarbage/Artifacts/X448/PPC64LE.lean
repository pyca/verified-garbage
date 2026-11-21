module

public import VerifiedGarbage.Proof.X448.PPC64LE.Verified
public import VerifiedGarbage.Proof.X448.PPC64LE.Exchange
public import VerifiedGarbage.Proof.X448.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # X448 (RFC 7748) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.X448.PPC64LE

def artifacts : List Artifact := [
  Spec.X448.exchangeApi.artifact PPC64LE.target {
    code := Impl.X448.PPC64LE.Fn.exchange
    verified := Proof.X448.PPC64LE.Scrub.exchange_scrubbed },
  Spec.X448.x448BaseApi.artifact PPC64LE.target {
    code := Impl.X448.PPC64LE.Fn.base
    verified := Proof.X448.PPC64LE.Scrub.base_scrubbed }]

end VG.Artifacts.X448.PPC64LE
