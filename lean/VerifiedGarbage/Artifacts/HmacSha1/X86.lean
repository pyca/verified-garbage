import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame

/-!
# HMAC-SHA-1 (RFC 2104) on x86

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86.lean`). `init` sets both states' hash values with SHA-1's
verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` word by word
into their buffers, and absorbs each with one call of SHA-1's verified
compression function.

`finalize` calls SHA-1's verified streaming `finalize` for the inner hash,
then computes the outer hash with one call of SHA-1's verified compression
function, on a block it lays out word by word in `scratch`: the outer key's
hash value, the inner digest, its padding and length.

`init` and `finalize` keep their working space in a frame of their own
(`Proof/Pbkdf2/Md/X86/Frame.lean`); `init_scratch` and `finalize_scratch`, the
same code with it as an argument, are what PBKDF2's code calls.
-/

namespace VG.Artifacts.HmacSha1.X86

def artifacts : List Artifact := [
  { Spec.Hmac.sha1I.initApi with
    target := X86.target
    doc := Spec.Hmac.sha1I.initApi.doc
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.initFrame Spec.Hmac.sha1I) 4
      Proof.Pbkdf2.Md.X86.sha1M.hmacInit
    contract := Spec.Hmac.sha1I.initContract X86.abi (48 + Proof.Pbkdf2.Md.X86.initFrame Spec.Hmac.sha1I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 48 + Proof.Pbkdf2.Md.X86.initFrame Spec.Hmac.sha1I
    verified := Proof.Pbkdf2.Md.X86.initFramed Proof.Pbkdf2.Md.X86.Instances.sha1_init (by decide) (by lit_decide)
      (by lit_decide) Proof.Pbkdf2.Md.X86.sha1_initFrameSat
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Hmac.sha1I.finalizeApi with
    target := X86.target
    doc := Spec.Hmac.sha1I.finalizeApi.doc
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha1I) 5
      Proof.Pbkdf2.Md.X86.sha1M.hmacFin
    contract := Spec.Hmac.sha1I.finalizeContract X86.abi (48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha1I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 48 + Proof.Pbkdf2.Md.X86.finFrame Spec.Hmac.sha1I
    verified := Proof.Pbkdf2.Md.X86.finFramed Proof.Pbkdf2.Md.X86.Instances.sha1_finalize (by decide) Proof.Hmac.sha1_local
      (by decide) (by lit_decide) (by lit_decide) Proof.Pbkdf2.Md.X86.sha1_finFrameSat
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Hmac.sha1I.initScratchApi with
    target := X86.target
    doc := Spec.Hmac.sha1I.initScratchApi.doc
    code := Proof.Pbkdf2.Md.X86.sha1M.hmacInit
    contract := Spec.Hmac.sha1I.initScratchContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initScratchContract; rfl⟩
    stack := 48
    verified := Proof.Pbkdf2.Md.X86.Instances.sha1_init
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Hmac.sha1I.finalizeScratchApi with
    target := X86.target
    doc := Spec.Hmac.sha1I.finalizeScratchApi.doc
    code := Proof.Pbkdf2.Md.X86.sha1M.hmacFin
    contract := Spec.Hmac.sha1I.finalizeScratchContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeScratchContract; rfl⟩
    stack := 48
    verified := Proof.Pbkdf2.Md.X86.Instances.sha1_finalize
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.HmacSha1.X86
