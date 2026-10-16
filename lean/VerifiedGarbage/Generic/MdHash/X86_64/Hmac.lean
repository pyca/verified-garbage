module

import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# HMAC (RFC 2104) over a Merkle–Damgård hash function on x86-64

A generic file (see `TCB/Emit.lean`): HMAC's `init` and `finalize`, the one
implementation for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86_64.lean`), calling the variant's compression function
(each once or twice), the hash function's streaming `init` and, in
`finalize`, its streaming `finalize` made with that compression function, are
emitted once for each variant (`Variants/MdHash/X86_64/`), named with its
suffix (e.g. `vg_hmac_sha256_init_shani`). `init` and `finalize` keep their
working space in a frame of their own; `init_scratch` and `finalize_scratch`,
the same code with it as an argument, are what PBKDF2's and ECDSA's code
calls.
-/

@[expose] public section

namespace VG.Generic.MdHash.X86_64.Hmac

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact := [
  v.I.initApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame v.I) .r8 v.H.hmacInit
    stack := 16 + Proof.Pbkdf2.Md.X86_64.hmacFrame v.I
    verified := v.hmacInitF
    spSafe := X86_64.withStackScratch_spSafe (by decide) v.hmacInitSp
    features := v.features },
  v.I.finalizeApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame v.I) .r8 v.H.hmacFin
    stack := 16 + Proof.Pbkdf2.Md.X86_64.hmacFrame v.I
    verified := v.hmacFinF
    spSafe := X86_64.withStackScratch_spSafe (by decide) v.hmacFinSp
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
