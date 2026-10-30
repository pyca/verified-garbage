module

public import VerifiedGarbage.Proof.X448.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # X448 (RFC 7748) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.X448.PPC64LE

def artifacts : List Artifact := [
  Spec.X448.x448Api.artifact PPC64LE.target {
    code := Impl.X448.PPC64LE.x448
    verified := Proof.X448.PPC64LE.x448_verified }]

end VG.Artifacts.X448.PPC64LE
