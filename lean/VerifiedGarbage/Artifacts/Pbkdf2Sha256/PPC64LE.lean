module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Sha256
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# PBKDF2-HMAC-SHA-256 (RFC 8018) on PPC64LE: the iteration and the whole derivation

The iteration is the one for every Merkle–Damgård hash function
(`Impl/Pbkdf2/PPC64LE.lean`): each step is two calls of SHA-256's verified
compression function (`vg_sha256_compress`), on a block laid out once in
`scratch`, with the padding of a `B + D`-byte message written before the
loop. It saves the link register in `scratch` and uses no stack.

The whole derivation, `pbkdf2`, is the one for every streaming hash function
(`Impl/Pbkdf2/Whole/PPC64LE.lean`), calling SHA-256's streaming `update`,
HMAC's `init` (which takes a key of any length, its working space in a frame
of its own) and `finalize`, and the iteration above. It runs in a frame
holding its working space (`Proof.Pbkdf2.Whole.PPC64LE.framed`); its code
pushes a frame of 48 bytes, below which HMAC's `init` uses its own frame and
96 bytes more.
-/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha256.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha256I.iterateApi.artifact PPC64LE.target {
    code := Proof.Pbkdf2.PPC64LE.Sha256.code
    verified := Proof.Pbkdf2.PPC64LE.Sha256.iterate },
  Spec.Hmac.sha256I.pbkdf2Api.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch (Proof.Pbkdf2.Whole.PPC64LE.pbkFrame Spec.Hmac.sha256I) .r10
      Proof.Pbkdf2.Whole.PPC64LE.Sha256.F.pbkdf2
    stack := Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha256I + 144 + Proof.Pbkdf2.Whole.PPC64LE.pbkFrame Spec.Hmac.sha256I
    verified := Proof.Pbkdf2.Whole.PPC64LE.Sha256.pbkdf2 },
  -- Scrypt's code calls `pbkdf2` with its own working space.
  Spec.Hmac.sha256I.pbkdf2ScratchApi.artifact PPC64LE.target {
    code := Proof.Pbkdf2.Whole.PPC64LE.Sha256.F.pbkdf2
    stack := Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha256I + 144
    verified := Proof.Pbkdf2.Whole.PPC64LE.Sha256.scratch }]

end VG.Artifacts.Pbkdf2Sha256.PPC64LE
