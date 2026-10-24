module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Init
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Init
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Finite-field Diffie–Hellman on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ffdh.PPC64LE

def artifacts : List Artifact := [
  Spec.Ffdh.parameterInitApi.artifact PPC64LE.target {
    notes := ["The model has no carry bit, so `bits` is first checked to be below `2^14` (a branch \
        on a public value), and the bounds are then sign bits of 64-bit differences."]
    code := Impl.Ffdh.PPC64LE.Generation.init
    verified := Proof.Ffdh.PPC64LE.Generation.init_verified },
  Spec.Ffdh.keyInitApi.artifact PPC64LE.target {
    notes := ["The model has no carry bit, so `p_len` is first checked to be below `2^11` (a branch \
        on a public value), and the bounds are then sign bits of 64-bit differences."]
    code := Impl.Ffdh.PPC64LE.KeyGeneration.init
    verified := Proof.Ffdh.PPC64LE.KeyGeneration.init_verified }]

end VG.Artifacts.Ffdh.PPC64LE
