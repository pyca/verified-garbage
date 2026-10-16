module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha512
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit

/-!
# HMAC-SHA-512 (RFC 2104) on x86

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86.lean`). `init` sets both states' hash values with
SHA-512's verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` word
by word into their buffers, and absorbs each with one call of SHA-512's
verified compression function.

`finalize` calls SHA-512's verified streaming `finalize` for the inner hash,
then computes the outer hash with one call of SHA-512's verified compression
function, on a block it lays out word by word in `scratch`: the outer key's
hash value, the inner digest, its padding and length.

`init` and `finalize` keep their working space in a frame of their own
(`Proof/Pbkdf2/Md/X86/Frame.lean`); `init_scratch` and `finalize_scratch`, the
same code with it as an argument, are what PBKDF2's code calls.
-/

@[expose] public section

namespace VG.Artifacts.HmacSha512.X86

def artifacts : List Artifact := [
  Spec.Hmac.sha512I.initApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.initFrame Spec.Hmac.sha512I) 4
      Proof.Pbkdf2.Md.X86.sha512M'.hmacInit
    stack := 48 + Proof.Pbkdf2.Md.X86.initFrame Spec.Hmac.sha512I
    verified := Proof.Pbkdf2.Md.X86.initFramed Proof.Pbkdf2.Md.X86.Instances.sha512_init (by lit_decide)
      (by lit_decide) Proof.Pbkdf2.Md.X86.sha512_initFrameSat },
  Spec.Hmac.sha512I.finalizeApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha512I) 5
      Proof.Pbkdf2.Md.X86.sha512M'.hmacFin
    stack := 48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha512I
    verified := Proof.Pbkdf2.Md.X86.finFramed Proof.Pbkdf2.Md.X86.Instances.sha512_finalize Proof.Hmac.sha512_local
      (by lit_decide) (by lit_decide) Proof.Pbkdf2.Md.X86.sha512_finFrameSat },
  Spec.Hmac.sha512I.initScratchApi.artifact X86.target {
    code := Proof.Pbkdf2.Md.X86.sha512M'.hmacInit
    stack := 48
    verified := Proof.Pbkdf2.Md.X86.Instances.sha512_init },
  Spec.Hmac.sha512I.finalizeScratchApi.artifact X86.target {
    code := Proof.Pbkdf2.Md.X86.sha512M'.hmacFin
    stack := 48
    verified := Proof.Pbkdf2.Md.X86.Instances.sha512_finalize }]

end VG.Artifacts.HmacSha512.X86
