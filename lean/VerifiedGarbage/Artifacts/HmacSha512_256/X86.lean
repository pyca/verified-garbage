import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame

/-!
# HMAC-SHA-512/256 (RFC 2104) on x86

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86.lean`). `init` sets both states' hash values with
SHA-512/256's verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad`
word by word into their buffers, and absorbs each with one call of
SHA-512/256's verified compression function.

`finalize` calls SHA-512/256's verified streaming `finalize` for the inner
hash, then computes the outer hash with one call of SHA-512/256's verified
compression function, on a block it lays out word by word in `scratch`: the
outer key's hash value, the inner digest, its padding and length.

`init` and `finalize` keep their working space in a frame of their own
(`Proof/Pbkdf2/Md/X86/Frame.lean`); `init_scratch` and `finalize_scratch`, the
same code with it as an argument, are what PBKDF2's code calls.
-/

namespace VG.Artifacts.HmacSha512_256.X86

def artifacts : List Artifact := [
  { Spec.Hmac.sha512_256I.initApi with
    target := X86.target
    doc := Spec.Hmac.sha512_256I.initApi.doc
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.initFrame Spec.Hmac.sha512_256I) 4
      Proof.Pbkdf2.Md.X86.sha512_256M.hmacInit
    contract := Spec.Hmac.sha512_256I.initContract X86.abi (48 + Proof.Pbkdf2.Md.X86.initFrame Spec.Hmac.sha512_256I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 48 + Proof.Pbkdf2.Md.X86.initFrame Spec.Hmac.sha512_256I
    verified := Proof.Pbkdf2.Md.X86.initFramed Proof.Pbkdf2.Md.X86.Instances.sha512_256_init (by decide) (by lit_decide)
      (by lit_decide) Proof.Pbkdf2.Md.X86.sha512_256_initFrameSat
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Hmac.sha512_256I.finalizeApi with
    target := X86.target
    doc := Spec.Hmac.sha512_256I.finalizeApi.doc
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha512_256I) 5
      Proof.Pbkdf2.Md.X86.sha512_256M.hmacFin
    contract := Spec.Hmac.sha512_256I.finalizeContract X86.abi (48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha512_256I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha512_256I
    verified := Proof.Pbkdf2.Md.X86.finFramed Proof.Pbkdf2.Md.X86.Instances.sha512_256_finalize (by decide) Proof.Hmac.sha512_256_local
      (by decide) (by lit_decide) (by lit_decide) Proof.Pbkdf2.Md.X86.sha512_256_finFrameSat
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Hmac.sha512_256I.initScratchApi with
    target := X86.target
    doc := Spec.Hmac.sha512_256I.initScratchApi.doc
    code := Proof.Pbkdf2.Md.X86.sha512_256M.hmacInit
    contract := Spec.Hmac.sha512_256I.initScratchContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initScratchContract; rfl⟩
    stack := 48
    verified := Proof.Pbkdf2.Md.X86.Instances.sha512_256_init
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Hmac.sha512_256I.finalizeScratchApi with
    target := X86.target
    doc := Spec.Hmac.sha512_256I.finalizeScratchApi.doc
    code := Proof.Pbkdf2.Md.X86.sha512_256M.hmacFin
    contract := Spec.Hmac.sha512_256I.finalizeScratchContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeScratchContract; rfl⟩
    stack := 48
    verified := Proof.Pbkdf2.Md.X86.Instances.sha512_256_finalize
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.HmacSha512_256.X86
