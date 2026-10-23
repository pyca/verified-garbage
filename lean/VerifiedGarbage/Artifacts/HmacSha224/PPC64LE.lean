module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha224
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# HMAC-SHA-224 (RFC 2104) on PPC64LE

The code for every Merkle–Damgård hash function with verified PPC64LE
streaming functions (`Impl/Hmac/Stream/PPC64LE.lean`), calling SHA-224's.
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

namespace VG.Artifacts.HmacSha224.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha224I.initAnyKeyApi.artifact PPC64LE.target {
    code := Proof.Hmac.Stream.PPC64LE.initCode Proof.Hmac.Stream.PPC64LE.Sha224.hash Spec.Hmac.sha224I 6
    stack := 96 + Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha224I
    verified := Proof.Hmac.Stream.PPC64LE.Sha224.initAny },
  Spec.Hmac.sha224I.finalizeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch (Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha224I) .r7
      Proof.Hmac.Stream.PPC64LE.Sha224.hash.finalize
    stack := 96 + Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha224I
    verified := Proof.Hmac.Stream.PPC64LE.Sha224.finalize },
  Spec.Hmac.sha224I.initScratchApi.artifact PPC64LE.target {
    code := Proof.Hmac.Stream.PPC64LE.Sha224.hash.init
    stack := 96
    verified := Proof.Hmac.Stream.PPC64LE.Sha224.initScratch },
  Spec.Hmac.sha224I.finalizeScratchApi.artifact PPC64LE.target {
    code := Proof.Hmac.Stream.PPC64LE.Sha224.hash.finalize
    stack := 96
    verified := Proof.Hmac.Stream.PPC64LE.Sha224.finalizeScratch }]

end VG.Artifacts.HmacSha224.PPC64LE
