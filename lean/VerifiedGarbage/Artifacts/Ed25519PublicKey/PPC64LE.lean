module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ed25519PublicKey.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed25519.publicKeyApi.artifact PPC64LE.target {
    notes := ["Includes SHA-512 of the seed (calls of SHA-512's streaming functions, their state and \
      working space in `scratch`), RFC 8032 pruning, and base-point multiplication (a call of \
      `vg_ed25519_scalar_base`). The digest, the scalar, the saved nonvolatile registers and `lr` \
      are in a frame of 176 bytes on the stack, whose first 136 are cleared before returning."]
    code := Impl.Ed25519.PPC64LE.Whole.publicKeyCode
    stack := 224
    verified := Proof.Ed25519.PPC64LE.Whole.publicKey_framed }]

end VG.Artifacts.Ed25519PublicKey.PPC64LE
