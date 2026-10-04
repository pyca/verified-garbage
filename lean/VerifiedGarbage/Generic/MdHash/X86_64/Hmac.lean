import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant

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

namespace VG.Generic.MdHash.X86_64.Hmac

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact := [
  { v.I.initApi with
    name := v.I.initApi.name ++ v.suffix
    target := X86_64.target
    doc := v.I.initApi.doc
    code := Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame v.I) .r8 v.H.hmacInit
    contract := v.I.initContract X86_64.abi (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame v.I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 16 + Proof.Pbkdf2.Md.X86_64.hmacFrame v.I
    verified := v.hmacInitF
    spSafe := X86_64.withStackScratch_spSafe (by decide) v.hmacInitSp
    features := v.features },
  { v.I.finalizeApi with
    name := v.I.finalizeApi.name ++ v.suffix
    target := X86_64.target
    doc := v.I.finalizeApi.doc
    code := Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame v.I) .r8 v.H.hmacFin
    contract := v.I.finalizeContract X86_64.abi (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame v.I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 16 + Proof.Pbkdf2.Md.X86_64.hmacFrame v.I
    verified := v.hmacFinF
    spSafe := X86_64.withStackScratch_spSafe (by decide) v.hmacFinSp
    features := v.features },
  { v.I.initScratchApi with
    name := v.I.initScratchApi.name ++ v.suffix
    target := X86_64.target
    doc := v.I.initScratchApi.doc
    code := v.H.hmacInit
    contract := v.I.initScratchContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initScratchContract; rfl⟩
    stack := 16
    verified := v.hmacInit
    spSafe := v.hmacInitSp
    features := v.features },
  { v.I.finalizeScratchApi with
    name := v.I.finalizeScratchApi.name ++ v.suffix
    target := X86_64.target
    doc := v.I.finalizeScratchApi.doc
    code := v.H.hmacFin
    contract := v.I.finalizeScratchContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeScratchContract; rfl⟩
    stack := 16
    verified := v.hmacFin
    spSafe := v.hmacFinSp
    features := v.features }]

end VG.Generic.MdHash.X86_64.Hmac
