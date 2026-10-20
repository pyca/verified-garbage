module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeySha256
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# HMAC-SHA-256 (RFC 2104) on x86, for every x86 SHA-256 backend

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86.lean`). `init` sets both states' hash values with
SHA-256's verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` word
by word into their buffers, and absorbs each with one call of the backend's
verified compression function.

`finalize` calls the backend's verified streaming `finalize` for the inner
hash, then computes the outer hash with one call of the backend's verified
compression function, on a block it lays out word by word in `scratch`: the
outer key's hash value, the inner digest, its padding and length.

`init` takes a key of any length (`initAnyKeyApi`): a key of at most a block
goes straight to `init_scratch`, in a frame of its own holding its working
space (`Proof/Pbkdf2/Md/X86/Frame.lean`); a longer key (`initCode`) is first
hashed with the backend's verified streaming functions into its
working space, as PBKDF2's `pbkdf2` hashes a long password
(`Impl/Pbkdf2/Md/AnyKey/X86.lean`), and `init_scratch`, the code above with
its working space as an argument, is called with its digest, in a larger
frame of its own, which it wipes before returning
(`Proof/Pbkdf2/Whole/X86/AnyKeyCT.lean`); `stack` is that of the larger.
`finalize` keeps its working space in a frame of its own too
(`Proof/Pbkdf2/Md/X86/Frame.lean`). `init_scratch` and
`finalize_scratch` are what PBKDF2's code calls.
-/

@[expose] public section

namespace VG.Generic.Sha256.X86.Hmac

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  Spec.Hmac.sha256I.initAnyKeyApi.artifact X86.target {
    suffix := v.suffix
    code := Proof.Pbkdf2.Whole.X86.initCode Spec.Hmac.sha256I v.M.hmacInit v.F
    stack := 76 + Proof.Pbkdf2.Whole.X86.Any.anyFrame Spec.Hmac.sha256I
    verified := Proof.Pbkdf2.Whole.X86.Any.sha256_initF v
    spSafe := Proof.Pbkdf2.Whole.X86.Any.sha256_initSp v
    features := v.features },
  Spec.Hmac.sha256I.finalizeApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha256I) 5
      v.M.hmacFin
    stack := 48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha256I
    verified := Proof.Pbkdf2.Md.X86.finFramed v.hmacFin Proof.Hmac.sha256_local Proof.Pbkdf2.Md.X86.sha256_finFrameSat
      (Proof.Pbkdf2.Md.X86.noEsp_of v.finalizeNoSp) v.finalizeStack
    spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.finSp
    features := v.features },
  Spec.Hmac.sha256I.initScratchApi.artifact X86.target {
    suffix := v.suffix
    code := v.M.hmacInit
    stack := 48
    verified := v.hmacInit
    spSafe := v.initSp
    features := v.features },
  Spec.Hmac.sha256I.finalizeScratchApi.artifact X86.target {
    suffix := v.suffix
    code := v.M.hmacFin
    stack := 48
    verified := v.hmacFin
    spSafe := v.finSp
    features := v.features }]

end VG.Generic.Sha256.X86.Hmac
