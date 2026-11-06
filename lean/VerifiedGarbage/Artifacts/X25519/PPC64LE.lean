module

public import VerifiedGarbage.Proof.X25519.PPC64LE.Verified
public import VerifiedGarbage.Proof.X25519.PPC64LE.BaseVerified
public import VerifiedGarbage.Proof.X25519.PPC64LE.Exchange
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # X25519 (RFC 7748) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.X25519.PPC64LE

def artifacts : List Artifact := [
  Spec.X25519.x25519Api.artifact PPC64LE.target {
    code := Impl.X25519.PPC64LE.x25519
    verified := Proof.X25519.PPC64LE.x25519_verified },
  Spec.X25519.exchangeApi.artifact PPC64LE.target {
    code := Impl.Xdh.PPC64LE.exchange "vg_x25519" Impl.X25519.PPC64LE.x25519 32
    stack := 48
    verified := Proof.X25519.PPC64LE.Exchange.exchange_verified },
  Spec.X25519.x25519BaseApi.artifact PPC64LE.target {
    consts := Impl.Ed25519.PPC64LE.combConsts
    code := Impl.X25519.PPC64LE.Base.x25519Base
    verified := Proof.X25519.PPC64LE.Base.x25519Base_verified }]

end VG.Artifacts.X25519.PPC64LE
