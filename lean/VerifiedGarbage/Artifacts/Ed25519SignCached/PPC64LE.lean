module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ed25519SignCached.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed25519.signCachedApi.artifact PPC64LE.target {
    notes := ["Includes SHA-512 (calls of SHA-512's streaming functions), scalar reduction, \
      base-point multiplication, and scalar multiply-add (calls of `vg_ed25519_scalar_reduce`, \
      `vg_ed25519_scalar_base` and `vg_ed25519_scalar_mul_add`). The secret scalar, the nonce, \
      their digests, a copy of `pk`, the saved nonvolatile registers and `lr` are in a frame of \
      320 bytes on the stack, whose first 224 are cleared before returning."]
    code := Impl.Ed25519.PPC64LE.Whole.signCachedCode
    stack := 368
    verified := Proof.Ed25519.PPC64LE.Whole.signCached_framed }]

end VG.Artifacts.Ed25519SignCached.PPC64LE
