module

public import VerifiedGarbage.Proof.Argon2.AArch64.Compress
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.Registration

/-! Argon2 block compression on baseline ARM64. -/

@[expose] public section

namespace VG.Artifacts.Argon2.AArch64

def artifacts : List Artifact := [
  Spec.Argon2.compressApi.artifact AArch64.target {
    code := Impl.Argon2.AArch64.compress
    stack := 0
    verified := Proof.Argon2.AArch64.compress_verified }]
end VG.Artifacts.Argon2.AArch64
