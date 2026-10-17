module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# The checked RSA private-key operation on ARMv7

A generic file (see `TCB/Emit.lean`): `vg_rsa_private_checked`, calling an
implementation `v` of `vg_rsa_private_crt` and the public operation it
comes with, is emitted once for each implementation
(`Variants/RsaPrivateCrt/Arm/`), named with its suffix, and needs its
CPU features.

It uses 3440 bytes of stack: its frame, the registers it saves and the
largest frame of its callees.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.Arm.Rsa

open VG.Proof.Rsa.Arm

def artifacts (v : CrtImpl) : List Artifact := [
  Spec.Rsa.privateCheckedApi.artifact Arm.target {
    suffix := v.suffix
    notes := ["This implementation computes the result `m` with `" ++ v.name ++
      "` into its frame, then `m^e mod n` with `" ++ v.pcName ++ "` and `" ++ v.pdName ++
      "`, which also checks `e`. It compares that with the input in constant time, and copies `m` \
      to `out` under a mask, which is clear unless the CRT and the public operation succeeded and \
      the two match. The result is computed from the mask without a branch. Then it overwrites \
      the frame's copy of `m` with zeros."]
    code := privCode v
    stack := stackBytes
    verified := code_verified v
    features := v.features }]

end VG.Generic.RsaPrivateCrt.Arm.Rsa
