module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha384
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyInstances
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit

/-!
# HMAC-SHA-384 (RFC 2104) on x86

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86.lean`). `init` sets both states' hash values with
SHA-384's verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` word
by word into their buffers, and absorbs each with one call of SHA-384's
verified compression function.

`finalize` calls SHA-384's verified streaming `finalize` for the inner hash,
then computes the outer hash with one call of SHA-384's verified compression
function, on a block it lays out word by word in `scratch`: the outer key's
hash value, the inner digest, its padding and length.

`init` takes a key of any length (`initAnyKeyApi`): a key of at most a block
goes straight to `init_scratch`, in a frame of its own holding its working
space (`Proof/Pbkdf2/Md/X86/Frame.lean`); a longer key (`initCode`) is first
hashed with SHA-384's verified streaming functions into its working
space, as PBKDF2's `pbkdf2` hashes a long password
(`Impl/Pbkdf2/Md/AnyKey/X86.lean`), and `init_scratch`, the code above with
its working space as an argument, is called with its digest, in a larger
frame of its own, which it wipes before returning
(`Proof/Pbkdf2/Whole/X86/AnyKeyCT.lean`); `stack` is that of the larger.
`finalize` keeps its working space in a frame of its own too
(`Proof/Pbkdf2/Md/X86/Frame.lean`). `init_scratch` and
`finalize_scratch` are what PBKDF2's code calls.
-/

@[expose] public section

namespace VG.Artifacts.HmacSha384.X86

def artifacts : List Artifact := [
  Spec.Hmac.sha384I.initAnyKeyApi.artifact X86.target {
    code := Proof.Pbkdf2.Whole.X86.initCode Spec.Hmac.sha384I Proof.Pbkdf2.Md.X86.sha384M.hmacInit Proof.Pbkdf2.Whole.X86.sha384F
    stack := 76 + Proof.Pbkdf2.Whole.X86.Any.anyFrame Spec.Hmac.sha384I
    verified := Proof.Pbkdf2.Whole.X86.Any.sha384_initF
    spSafe := Proof.Pbkdf2.Whole.X86.Any.sha384_initSp },
  Spec.Hmac.sha384I.finalizeApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha384I) 5
      Proof.Pbkdf2.Md.X86.sha384M.hmacFin
    stack := 48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha384I
    verified := Proof.Pbkdf2.Md.X86.finFramed Proof.Pbkdf2.Md.X86.Instances.sha384_finalize Proof.Hmac.sha384_local
      Proof.Pbkdf2.Md.X86.sha384_finFrameSat },
  Spec.Hmac.sha384I.initScratchApi.artifact X86.target {
    code := Proof.Pbkdf2.Md.X86.sha384M.hmacInit
    stack := 48
    verified := Proof.Pbkdf2.Md.X86.Instances.sha384_init },
  Spec.Hmac.sha384I.finalizeScratchApi.artifact X86.target {
    code := Proof.Pbkdf2.Md.X86.sha384M.hmacFin
    stack := 48
    verified := Proof.Pbkdf2.Md.X86.Instances.sha384_finalize }]

end VG.Artifacts.HmacSha384.X86
