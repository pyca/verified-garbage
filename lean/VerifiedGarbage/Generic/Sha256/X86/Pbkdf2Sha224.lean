module

import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# PBKDF2-HMAC-SHA-224 (RFC 8018) on x86, for every x86 SHA-256 backend: the iteration and the whole derivation

The iteration is the one for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86.lean`): each step is two calls of the backend's
verified SHA-256 compression function, on a block laid out once, word by
word, in `scratch` (`U`, its padding and length), starting from the key's
inner and outer hash values.

The whole derivation, `pbkdf2`, is the one for every streaming hash function
(`Impl/Pbkdf2/Whole/X86.lean`), calling SHA-224's `init`, the backend's
SHA-256 streaming functions, HMAC-SHA-224's `init` and `finalize` and the
iteration above, made with the backend. `stack` is that of the shared
contracts: 48 bytes for the iteration, and 76 for `pbkdf2`, which pushes up
to 24 bytes of arguments for the functions it calls, and their return
address, and gives them 48. `pbkdf2` runs that code in a frame holding its
working space (`Proof.Pbkdf2.Whole.X86.pbkFramed`).
-/

@[expose] public section

namespace VG.Generic.Sha256.X86.Pbkdf2Sha224

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  Spec.Hmac.sha224I.iterateApi.artifact X86.target {
    suffix := v.suffix
    code := v.M224.iterate
    stack := 48
    verified := v.iterate224
    spSafe := v.iter224Sp
    features := v.features },
  Spec.Hmac.sha224I.pbkdf2Api.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Whole.X86.pbkFrame Spec.Hmac.sha224I) 7 v.F224.pbkdf2
    stack := 76 + Proof.Pbkdf2.Whole.X86.pbkFrame Spec.Hmac.sha224I
    verified := Proof.Pbkdf2.Whole.X86.pbkFramed (Proof.Pbkdf2.Whole.X86.sha224_verified v)
      Proof.Pbkdf2.Whole.X86.sha224_pbkFrameSat
      (Proof.Pbkdf2.Whole.X86.noEsp_of_all v.pbkdf2_224Sp) (Proof.Pbkdf2.Whole.X86.sha224_stack v)
    spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.pbkdf2_224Sp
    features := v.features }]

end VG.Generic.Sha256.X86.Pbkdf2Sha224
