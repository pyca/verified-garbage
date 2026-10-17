module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
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
functions may use for a frame saving `x30`. `init_scratch` and
`finalize_scratch`, with their working space as an argument, are what
PBKDF2's code calls; `finalize` keeps its working space in a frame of its own,
above those. `init` takes a key of any length
(`Impl/Pbkdf2/Md/AnyKey/AArch64.lean`): it runs `init_scratch` in a frame of
its own for a key of at most a block, zeroing the part of it where the
compression function leaves the schedule of the padded keys (`MdHash.wipe`,
`Compress.wipe`: none for the `_sha2` and `_sha3` variants and MD5), and for
a longer key hashes it with the
streaming functions, as `pbkdf2` hashes a long password, and calls
`init_scratch` with its digest, in a larger frame of its own that it zeroes
before returning (`initCode`). `stack` is that of the larger.
-/

@[expose] public section

namespace VG.Generic.MdHash.AArch64.Hmac

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact := [
  v.I.initAnyKeyApi.artifact AArch64.target {
    suffix := v.suffix
    code := Proof.Pbkdf2.Md.AArch64.initCode v.H v.I v.wipe
    stack := 16 + Proof.Pbkdf2.Md.AArch64.anyFrame v.I
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
