module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Hmac.PPC64LE.Shared
public import VerifiedGarbage.Proof.Hmac.PPC64LE.AnyKey
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# HMAC-SHA-256 (RFC 2104) on PPC64LE

`init` takes a key of any length (`initAnyKeyApi`), and chooses on entry by
its public length (`Proof/Hmac/PPC64LE/AnyKey.lean`): a key of at most a
block goes to `init_scratch`'s code in a frame of its own holding its working
space; a longer key is first hashed with SHA-256's verified streaming
functions into the working space of a frame that it zeroes before returning,
and `init_scratch` is called with its digest (`Proof/Hmac/PPC64LE/InitLong.lean`).
Both paths take the same stack. `finalize` keeps its working space in a
frame of its own too. `init_scratch` and `finalize_scratch` take theirs as an
argument.
-/

@[expose] public section

namespace VG.Artifacts.HmacSha256.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha256I.initAnyKeyApi.artifact PPC64LE.target {
    code := Impl.Hmac.PPC64LE.initAny
    stack := 48 + 864
    verified := Proof.Hmac.PPC64LE.AnyKey.initAny },
  Spec.Hmac.sha256I.finalizeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 864 .r7 Impl.Hmac.PPC64LE.finalize
    stack := 96 + 864
    verified := Proof.Hmac.PPC64LE.Shared.finalize },
  Spec.Hmac.sha256I.initScratchApi.artifact PPC64LE.target {
    code := Impl.Hmac.PPC64LE.init
    stack := 48
    verified := Proof.Hmac.PPC64LE.Shared.initScratch },
  Spec.Hmac.sha256I.finalizeScratchApi.artifact PPC64LE.target {
    code := Impl.Hmac.PPC64LE.finalize
    stack := 96
    verified := Proof.Hmac.PPC64LE.Shared.finalizeScratch }]

end VG.Artifacts.HmacSha256.PPC64LE
