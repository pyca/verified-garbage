module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Md5
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# HMAC-MD5 (RFC 2104) on PPC64LE

The code for every Merkle–Damgård hash function with verified PPC64LE
streaming functions (`Impl/Hmac/Stream/PPC64LE.lean`), calling MD5's.
`init_scratch` sets both states' hash values with the streaming `init` and
absorbs `K₀ ⊕ ipad` and `K₀ ⊕ opad` with `update`; `finalize_scratch`
finalizes the inner state, makes it represent the outer block, absorbs the
inner digest and finalizes again. Both take their working space as an
argument. `init` takes a key of any length (`initAnyKeyApi`), and chooses on
entry by its public length: a key of at most a block goes to
`init_scratch`'s code in a frame of its own holding its working space; a
longer key is first hashed with the streaming functions into the working
space of a frame that it zeroes before returning, and `init_scratch` is
called with its digest. Both paths take the same stack. `finalize` keeps its
working space in a frame of its own too.
-/

@[expose] public section

namespace VG.Artifacts.HmacMd5.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.md5I.initAnyKeyApi.artifact PPC64LE.target {
    code := Proof.Hmac.Stream.PPC64LE.initCode Proof.Hmac.Stream.PPC64LE.Md5.hash Spec.Hmac.md5I 6
    stack := 96 + Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.md5I
    verified := Proof.Hmac.Stream.PPC64LE.Md5.initAny },
  Spec.Hmac.md5I.finalizeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch (Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.md5I) .r7
      Proof.Hmac.Stream.PPC64LE.Md5.hash.finalize
    stack := 96 + Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.md5I
    verified := Proof.Hmac.Stream.PPC64LE.Md5.finalize },
  Spec.Hmac.md5I.initScratchApi.artifact PPC64LE.target {
    code := Proof.Hmac.Stream.PPC64LE.Md5.hash.init
    stack := 96
    verified := Proof.Hmac.Stream.PPC64LE.Md5.initScratch },
  Spec.Hmac.md5I.finalizeScratchApi.artifact PPC64LE.target {
    code := Proof.Hmac.Stream.PPC64LE.Md5.hash.finalize
    stack := 96
    verified := Proof.Hmac.Stream.PPC64LE.Md5.finalizeScratch }]

end VG.Artifacts.HmacMd5.PPC64LE
