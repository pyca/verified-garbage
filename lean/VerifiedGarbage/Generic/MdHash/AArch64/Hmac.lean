module

import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# HMAC (RFC 2104) over a Merkle–Damgård hash function on AArch64

A generic file (see `TCB/Emit.lean`): HMAC's `init` and `finalize`, the one
implementation for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/AArch64.lean`), calling the variant's compression function
(each once or twice), the hash function's streaming `init` and, in
`finalize`, its streaming `finalize` made with that compression function, are
emitted once for each variant (`Variants/MdHash/AArch64/`), named with its
suffix.

`stack` is the 16 bytes below the stack pointer that the streaming
functions may use for a frame saving `x30`. `init` and `finalize` keep their
working space in a frame of their own, above those; `init_scratch` and
`finalize_scratch`, the same code with it as an argument, are what PBKDF2's
code calls.
-/

@[expose] public section

namespace VG.Generic.MdHash.AArch64.Hmac

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact := [
  v.I.initApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch (Proof.Pbkdf2.Md.AArch64.hmacFrame v.I) .x4 v.H.hmacInit
    stack := 16 + Proof.Pbkdf2.Md.AArch64.hmacFrame v.I
    verified := v.hmacInitF
    features := v.features },
  v.I.finalizeApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch (Proof.Pbkdf2.Md.AArch64.hmacFrame v.I) .x4 v.H.hmacFin
    stack := 16 + Proof.Pbkdf2.Md.AArch64.hmacFrame v.I
    verified := v.hmacFinF
    features := v.features },
  v.I.initScratchApi.artifact AArch64.target {
    suffix := v.suffix
    code := v.H.hmacInit
    stack := 16
    verified := v.hmacInit
    features := v.features },
  v.I.finalizeScratchApi.artifact AArch64.target {
    suffix := v.suffix
    code := v.H.hmacFin
    stack := 16
    verified := v.hmacFin
    features := v.features }]

end VG.Generic.MdHash.AArch64.Hmac
