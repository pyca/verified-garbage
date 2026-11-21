module

public import VerifiedGarbage.Proof.X25519.PPC64LE.Verified
public import VerifiedGarbage.Proof.X25519.PPC64LE.BaseVerified
public import VerifiedGarbage.Proof.X25519.PPC64LE.Exchange
public import VerifiedGarbage.Proof.X25519.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # X25519 (RFC 7748) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.X25519.PPC64LE

def artifacts : List Artifact := [
  Spec.X25519.exchangeApi.artifact PPC64LE.target {
    code := Impl.X25519.PPC64LE.Fn.exchange
    verified := Proof.X25519.PPC64LE.Scrub.exchange_scrubbed },
  Spec.X25519.x25519BaseApi.artifact PPC64LE.target {
    code := Impl.X25519.PPC64LE.Fn.base
    verified := Proof.X25519.PPC64LE.Scrub.base_scrubbed }]

end VG.Artifacts.X25519.PPC64LE
