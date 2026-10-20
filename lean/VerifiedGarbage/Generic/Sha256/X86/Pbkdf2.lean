module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame
import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFin
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Loop
public import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFin
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Loop
import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant

/-!
# PBKDF2-HMAC-SHA-256 (RFC 8018) on x86, for every x86 SHA-256 backend: the iteration and the whole derivation

The iteration is the one for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86.lean`): each step is two calls of the backend's
verified compression function, on a block laid out once, word by word, in
`scratch` (`U`, its padding and length), starting from the key's inner and
outer hash values.

The whole derivation, `pbkdf2`, is the one for every streaming hash function
(`Impl/Pbkdf2/Whole/X86.lean`), calling the backend's streaming functions,
HMAC's `init` and `finalize` and the iteration above, made with the backend.
`stack` is that of the shared contracts: 48 bytes for the iteration, and 76
for `pbkdf2`, which pushes up to 24 bytes of arguments for the functions it
calls, and their return address, and gives them 48. `pbkdf2` runs that code
in a frame holding its working space (`Proof.Pbkdf2.Whole.X86.pbkFramed`);
scrypt's code calls the code itself, with its own working space, as
`vg_pbkdf2_hmac_sha256_scratch`.
-/

@[expose] public section

namespace VG.Generic.Sha256.X86.Pbkdf2

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  Spec.Hmac.sha256I.iterateApi.artifact X86.target {
    suffix := v.suffix
    code := v.M.iterate
    stack := 48
    verified := v.iterate
    spSafe := v.iterSp
    features := v.features },
  Spec.Hmac.sha256I.pbkdf2Api.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Whole.X86.pbkFrame Spec.Hmac.sha256I) 7 v.F.pbkdf2
    stack := 76 + Proof.Pbkdf2.Whole.X86.pbkFrame Spec.Hmac.sha256I
    verified := Proof.Pbkdf2.Whole.X86.pbkFramed (Proof.Pbkdf2.Whole.X86.sha256_verified v)
      Proof.Pbkdf2.Whole.X86.sha256_pbkFrameSat
      (Proof.Pbkdf2.Whole.X86.noEsp_of_all v.pbkdf2Sp) (Proof.Pbkdf2.Whole.X86.sha256_stack v)
    spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.pbkdf2Sp
    features := v.features },
  -- Scrypt's code calls `pbkdf2` with its own working space.
  Spec.Hmac.sha256I.pbkdf2ScratchApi.artifact X86.target {
    suffix := v.suffix
    code := v.F.pbkdf2
    stack := 76
    verified := Proof.Pbkdf2.Whole.X86.sha256_verified v
    spSafe := v.pbkdf2Sp
    features := v.features }]

end VG.Generic.Sha256.X86.Pbkdf2
