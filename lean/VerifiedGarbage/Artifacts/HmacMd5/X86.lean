module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Md5
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit

/-!
# HMAC-MD5 (RFC 2104) on x86

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86.lean`). `init` sets both states' hash values with MD5's
verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` word by word
into their buffers, and absorbs each with one call of MD5's verified
compression function.

`finalize` calls MD5's verified streaming `finalize` for the inner hash, then
computes the outer hash with one call of MD5's verified compression function,
on a block it lays out word by word in `scratch`: the outer key's hash value,
the inner digest, its padding and length.

`init` and `finalize` keep their working space in a frame of their own
(`Proof/Pbkdf2/Md/X86/Frame.lean`); `init_scratch` and `finalize_scratch`, the
same code with it as an argument, are what PBKDF2's code calls.
-/

@[expose] public section

namespace VG.Artifacts.HmacMd5.X86

def artifacts : List Artifact := [
  Spec.Hmac.md5I.initApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.initFrame Spec.Hmac.md5I) 4
      Proof.Pbkdf2.Md.X86.md5M.hmacInit
    stack := 48 + Proof.Pbkdf2.Md.X86.initFrame Spec.Hmac.md5I
    verified := Proof.Pbkdf2.Md.X86.initFramed Proof.Pbkdf2.Md.X86.Instances.md5_init (by decide) (by lit_decide)
      (by lit_decide) Proof.Pbkdf2.Md.X86.md5_initFrameSat },
  Spec.Hmac.md5I.finalizeApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.md5I) 5
      Proof.Pbkdf2.Md.X86.md5M.hmacFin
    stack := 48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.md5I
    verified := Proof.Pbkdf2.Md.X86.finFramed Proof.Pbkdf2.Md.X86.Instances.md5_finalize (by decide) Proof.Hmac.md5_local
      (by decide) (by lit_decide) (by lit_decide) Proof.Pbkdf2.Md.X86.md5_finFrameSat },
  Spec.Hmac.md5I.initScratchApi.artifact X86.target {
    code := Proof.Pbkdf2.Md.X86.md5M.hmacInit
    stack := 48
    verified := Proof.Pbkdf2.Md.X86.Instances.md5_init },
  Spec.Hmac.md5I.finalizeScratchApi.artifact X86.target {
    code := Proof.Pbkdf2.Md.X86.md5M.hmacFin
    stack := 48
    verified := Proof.Pbkdf2.Md.X86.Instances.md5_finalize }]

end VG.Artifacts.HmacMd5.X86
