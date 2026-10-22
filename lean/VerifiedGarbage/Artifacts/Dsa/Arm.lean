module

public import VerifiedGarbage.Proof.Dsa.Arm.Verified
public import VerifiedGarbage.Proof.Dsa.Arm.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateVerified
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Dsa.Arm.Leaves

/-! DSA signing with a supplied or a sampled nonce, verification, domain checks, key derivation
and key generation, on ARMv7. -/

@[expose] public section

namespace VG.Artifacts.Dsa.Arm

def artifacts : List Artifact := [
  Spec.Dsa.randomSignApi.artifact Arm.target {
    notes := ["Rejection sampling and signing retries are verified against the bounded \
      random-tape specification; each signing attempt calls `vg_dsa_sign`. Every failure zeros \
      the entire output. Callee-saved registers and the loop's state reside in a stack frame."]
    code := Impl.Dsa.Arm.RandomSign.code Spec.Dsa.signApi.name (Impl.Dsa.Arm.Entry.operation true)
    verified := Proof.Dsa.Arm.randomSigning_verified
    stack := 144 },
  Spec.Dsa.signApi.artifact Arm.target {
    notes := ["Each supported (p, q) width has its own code, chosen by the public lengths. \
      Arithmetic loops over the words of a runtime-modulus Montgomery workspace in `scratch`; \
      exponentiation uses fixed-iteration square-and-multiply with a masked selection. \
      The digest's prefix, clamped to q's actual byte width, is reduced byte by byte. \
      Validation accumulates a mask; every failure zeros the entire output. Callee-saved \
      registers reside in `scratch`."]
    code := Impl.Dsa.Arm.Entry.operation true
    verified := Proof.Dsa.Arm.sign_verified },
  Spec.Dsa.verifyApi.artifact Arm.target {
    notes := ["Each supported (p, q) width has its own code, chosen by the public lengths. \
      Arithmetic loops over the words of a runtime-modulus Montgomery workspace in `scratch`. \
      Signature scalars and the digest do not affect the leakage trace. Callee-saved \
      registers reside in `scratch`."]
    code := Impl.Dsa.Arm.Entry.operation false
    verified := Proof.Dsa.Arm.verify_verified },
  Spec.Dsa.checkParametersApi.artifact Arm.target {
    notes := ["Uses the signer's public-width dispatch and Montgomery arithmetic. \
      The generator's range and subgroup power are checked once; the mask \
      also checks that q divides p-1. Callee-saved registers reside in `scratch`."]
    code := Impl.Dsa.Arm.Generate.checkParameters
    verified := Proof.Dsa.Arm.check_verified },
  Spec.Dsa.deriveKeyApi.artifact Arm.target {
    notes := ["Checks the domain once and derives the public key with the signer's \
      fixed-schedule exponentiation. The public key's subgroup identity follows from the \
      generator's. The key is copied out under the mask, which zeros it on failure; \
      callee-saved registers reside in `scratch`."]
    code := Impl.Dsa.Arm.Generate.deriveKey
    verified := Proof.Dsa.Arm.derive_verified },
  Spec.Dsa.generateKeyApi.artifact Arm.target {
    notes := ["Checks the domain with `vg_dsa_check_parameters`, draws x by rejection \
      sampling as the randomized signer draws its nonce, and derives the key with \
      `vg_dsa_derive_key`, which checks the domain again. Every failure zeros the entire \
      output. Callee-saved registers and the sampler's state reside in a stack frame."]
    code := Impl.Dsa.Arm.GenerateKey.code Spec.Dsa.checkParametersApi.name Spec.Dsa.deriveKeyApi.name
      Impl.Dsa.Arm.Generate.checkParameters Impl.Dsa.Arm.Generate.deriveKey
    verified := Proof.Dsa.Arm.Key.generating_verified
    stack := 144 }]

end VG.Artifacts.Dsa.Arm
