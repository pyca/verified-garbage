module

public import VerifiedGarbage.Proof.Dsa.Arm.Verified
public import VerifiedGarbage.Proof.Dsa.Arm.RandomSignVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Dsa.Arm.Leaves

/-! DSA signing with a supplied or a sampled nonce, and verification, on ARMv7. -/

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
    verified := Proof.Dsa.Arm.verify_verified }]

end VG.Artifacts.Dsa.Arm
