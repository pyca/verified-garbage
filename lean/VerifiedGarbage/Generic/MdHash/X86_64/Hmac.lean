module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Framework.X86_64.Registration

/-!
# HMAC (RFC 2104) over a Merkle–Damgård hash function on x86-64

A generic file (see `TCB/Emit.lean`): HMAC's `init` and `finalize`, the one
implementation for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86_64.lean`), calling the variant's compression function
(each once or twice), the hash function's streaming `init` and, in
`finalize`, its streaming `finalize` made with that compression function, are
emitted once for each variant (`Variants/MdHash/X86_64/`), named with its
suffix (e.g. `vg_hmac_sha256_init_shani`). `init_scratch` and
`finalize_scratch`, with their working space as an argument, are what
PBKDF2's and ECDSA's code calls; `finalize` keeps its working space in a frame
of its own. `init` takes a key of any length (`Impl/Pbkdf2/Md/AnyKey/X86_64.lean`):
it hashes a key longer than a block with the streaming functions, as
`pbkdf2` hashes a long password, and calls `init_scratch` with the key or its
digest, in a frame of its own that it zeroes before returning.
-/

@[expose] public section

namespace VG.Generic.MdHash.X86_64.Hmac

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact := [
  v.I.initAnyKeyApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratchWiped (Proof.Pbkdf2.Md.X86_64.anyFrame v.I) .r8
      v.I.initAnyKeyScratch v.H.hmacInitAny
    stack := 24 + Proof.Pbkdf2.Md.X86_64.anyFrame v.I
    verified := v.hmacInitAnyF
    spSafe := v.hmacInitAnySp
    features := v.features },
  v.I.finalizeApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame v.I) .r8 v.H.hmacFin
    stack := 16 + Proof.Pbkdf2.Md.X86_64.hmacFrame v.I
    verified := v.hmacFinF
    spSafe := X86_64.withStackScratch_spSafe_of v.hmacFinSp
    features := v.features },
  v.I.initScratchApi.artifact X86_64.target {
    suffix := v.suffix
    code := v.H.hmacInit
    stack := 16
    verified := v.hmacInit
    spSafe := v.hmacInitSp
    features := v.features },
  v.I.finalizeScratchApi.artifact X86_64.target {
    suffix := v.suffix
    code := v.H.hmacFin
    stack := 16
    verified := v.hmacFin
    spSafe := v.hmacFinSp
    features := v.features }]

end VG.Generic.MdHash.X86_64.Hmac
