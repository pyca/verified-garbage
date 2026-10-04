import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame

/-!
# HMAC-SHA-224 (RFC 2104) on x86, for every x86 SHA-256 backend

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86.lean`). `init` sets both states' hash values with
SHA-224's verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` word
by word into their buffers, and absorbs each with one call of the backend's
verified SHA-256 compression function.

`finalize` calls the backend's verified SHA-256 streaming `finalize` for the
inner hash, then computes the outer hash with one call of the backend's
verified compression function, on a block it lays out word by word in
`scratch`: the outer key's hash value, the inner digest (the first 28 bytes
of the inner final hash value), its padding and length.

`init` and `finalize` keep their working space in a frame of their own
(`Proof/Pbkdf2/Md/X86/Frame.lean`); `init_scratch` and `finalize_scratch`, the
same code with it as an argument, are what PBKDF2's code calls.
-/

namespace VG.Generic.Sha256.X86.HmacSha224

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  { Spec.Hmac.sha224I.initApi with
    name := Spec.Hmac.sha224I.initApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha224I.initApi.doc
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.initFrame Spec.Hmac.sha224I) 4
      v.M224.hmacInit
    contract := Spec.Hmac.sha224I.initContract X86.abi (48 + Proof.Pbkdf2.Md.X86.initFrame Spec.Hmac.sha224I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 48 + Proof.Pbkdf2.Md.X86.initFrame Spec.Hmac.sha224I
    verified := Proof.Pbkdf2.Md.X86.initFramed v.hmacInit224 (by decide)
      (Proof.Pbkdf2.Md.X86.noEsp_of v.init224NoSp) v.init224Stack Proof.Pbkdf2.Md.X86.sha224_initFrameSat
    spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe (by decide) v.init224Sp
    features := v.features },
  { Spec.Hmac.sha224I.finalizeApi with
    name := Spec.Hmac.sha224I.finalizeApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha224I.finalizeApi.doc
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha224I) 5
      v.M224.hmacFin
    contract := Spec.Hmac.sha224I.finalizeContract X86.abi (48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha224I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha224I
    verified := Proof.Pbkdf2.Md.X86.finFramed v.hmacFin224 (by decide) Proof.Hmac.sha224_local
      (by decide) (Proof.Pbkdf2.Md.X86.noEsp_of v.finalize224NoSp) v.finalize224Stack Proof.Pbkdf2.Md.X86.sha224_finFrameSat
    spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe (by decide) v.fin224Sp
    features := v.features },
  { Spec.Hmac.sha224I.initScratchApi with
    name := Spec.Hmac.sha224I.initScratchApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha224I.initScratchApi.doc
    code := v.M224.hmacInit
    contract := Spec.Hmac.sha224I.initScratchContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initScratchContract; rfl⟩
    stack := 48
    verified := v.hmacInit224
    spSafe := v.init224Sp
    features := v.features },
  { Spec.Hmac.sha224I.finalizeScratchApi with
    name := Spec.Hmac.sha224I.finalizeScratchApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha224I.finalizeScratchApi.doc
    code := v.M224.hmacFin
    contract := Spec.Hmac.sha224I.finalizeScratchContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeScratchContract; rfl⟩
    stack := 48
    verified := v.hmacFin224
    spSafe := v.fin224Sp
    features := v.features }]

end VG.Generic.Sha256.X86.HmacSha224
