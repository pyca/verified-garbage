module

public import VerifiedGarbage.Proof.X25519.X86.Field32.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.X25519.X86.Field32.Lit

/-! # Powers in curve25519's field, in radix `2^32`, on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Gf25519R32.X86

open VG.Spec.X25519.Field32 VG.Impl.X25519.X86.Field32 VG.Proof.X25519.X86.Field32

def artifacts : List Artifact := [
  pow250Api.artifact X86.target {
    code := pow250Fn
    verified := pow250Fn_verified }]

end VG.Artifacts.Gf25519R32.X86
