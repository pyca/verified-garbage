module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyVerified
import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.Proof.Framework.Registration

/-! Complete strict Ed25519 equation verification with a caller-supplied SHA-512 challenge. -/

@[expose] public section

namespace VG.Artifacts.Ed25519Verify.AArch64

def artifacts : List Artifact := [
  Spec.Ed25519.verifyEquationApi.artifact AArch64.target {
    notes := ["Uses baseline integer and AdvSIMD instructions. \
      Checks canonical point encodings and S < L, then evaluates the uncofactored equation \
      using all 512 challenge bits. No additional subgroup or small-order policy is imposed. \
      Computes [k]A - [S]B with one chain of doublings and 4-bit windows of the public \
      scalars, split into nibbles with AdvSIMD instructions, from a table of [1]A to [15]A \
      and one of -[1]B to -[15]B, cached as [Y - X, Y + X, 2dT, 2Z] and copied into \
      `scratch` from the static `VG_ED25519_VERIFY_NEG_BASE`, skipping the leading zero \
      nibbles of k above its low 64, and compares it with -R projectively."]
    consts := Impl.Ed25519.AArch64.bConsts
    code := Impl.Ed25519.AArch64.verifyEquation
    verified := Proof.Ed25519.AArch64.verify_verified }]

end VG.Artifacts.Ed25519Verify.AArch64
