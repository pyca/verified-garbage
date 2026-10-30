module

public import VerifiedGarbage.Proof.X25519.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # X25519 (RFC 7748) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.X25519.PPC64LE

def artifacts : List Artifact := [
  Spec.X25519.x25519Api.artifact PPC64LE.target {
    code := Impl.X25519.PPC64LE.x25519
    verified := Proof.X25519.PPC64LE.x25519_verified }]

end VG.Artifacts.X25519.PPC64LE
