import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame

/-!
# HMAC-SHA-256 (RFC 2104) on x86, for every x86 SHA-256 backend

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86.lean`). `init` sets both states' hash values with
SHA-256's verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` word
by word into their buffers, and absorbs each with one call of the backend's
verified compression function.

`finalize` calls the backend's verified streaming `finalize` for the inner
hash, then computes the outer hash with one call of the backend's verified
compression function, on a block it lays out word by word in `scratch`: the
outer key's hash value, the inner digest, its padding and length.

`init` and `finalize` keep their working space in a frame of their own
(`Proof/Pbkdf2/Md/X86/Frame.lean`); `init_scratch` and `finalize_scratch`, the
same code with it as an argument, are what PBKDF2's code calls.
-/

namespace VG.Generic.Sha256.X86.Hmac

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  { Spec.Hmac.sha256I.initApi with
    name := Spec.Hmac.sha256I.initApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha256I.initApi.doc
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.initFrame Spec.Hmac.sha256I) 4
      v.M.hmacInit
    contract := Spec.Hmac.sha256I.initContract X86.abi (48 + Proof.Pbkdf2.Md.X86.initFrame Spec.Hmac.sha256I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 48 + Proof.Pbkdf2.Md.X86.initFrame Spec.Hmac.sha256I
    verified := Proof.Pbkdf2.Md.X86.initFramed v.hmacInit (by decide)
      (Proof.Pbkdf2.Md.X86.noEsp_of v.initNoSp) v.initStack Proof.Pbkdf2.Md.X86.sha256_initFrameSat
    spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe (by decide) v.initSp
    features := v.features },
  { Spec.Hmac.sha256I.finalizeApi with
    name := Spec.Hmac.sha256I.finalizeApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha256I.finalizeApi.doc
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha256I) 5
      v.M.hmacFin
    contract := Spec.Hmac.sha256I.finalizeContract X86.abi (48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha256I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha256I
    verified := Proof.Pbkdf2.Md.X86.finFramed v.hmacFin (by decide) Proof.Hmac.sha256_local
      (by decide) (Proof.Pbkdf2.Md.X86.noEsp_of v.finalizeNoSp) v.finalizeStack Proof.Pbkdf2.Md.X86.sha256_finFrameSat
    spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe (by decide) v.finSp
    features := v.features },
  { Spec.Hmac.sha256I.initScratchApi with
    name := Spec.Hmac.sha256I.initScratchApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha256I.initScratchApi.doc
    code := v.M.hmacInit
    contract := Spec.Hmac.sha256I.initScratchContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initScratchContract; rfl⟩
    stack := 48
    verified := v.hmacInit
    spSafe := v.initSp
    features := v.features },
  { Spec.Hmac.sha256I.finalizeScratchApi with
    name := Spec.Hmac.sha256I.finalizeScratchApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha256I.finalizeScratchApi.doc
    code := v.M.hmacFin
    contract := Spec.Hmac.sha256I.finalizeScratchContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeScratchContract; rfl⟩
    stack := 48
    verified := v.hmacFin
    spSafe := v.finSp
    features := v.features }]

end VG.Generic.Sha256.X86.Hmac
