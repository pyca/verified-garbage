module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # Ed25519 signing with the seed's cached SHA-512 digest -/

@[expose] public section

namespace VG.Artifacts.Ed25519SignExpanded.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed25519.signExpandedApi.artifact PPC64LE.target {
    consts := Impl.Ed25519.PPC64LE.combConsts
    code := Impl.Ed25519.PPC64LE.Whole.signExpandedCode
    stack := 368
    verified := Proof.Ed25519.PPC64LE.Whole.signExpanded_framed }]

end VG.Artifacts.Ed25519SignExpanded.PPC64LE
