module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.FieldVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's point addition, in radix `2^32`, on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ed25519R32.PPC64LE

open VG.Spec.Ed25519.Point32 VG.Impl.Ed25519.PPC64LE VG.Proof.Ed25519.PPC64LE

def artifacts : List Artifact := [
  addApi.artifact PPC64LE.target {
    code := addFn
    verified := addFn_verified }]

end VG.Artifacts.Ed25519R32.PPC64LE
