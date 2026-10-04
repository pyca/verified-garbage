import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Instances
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Frame

/-!
# HMAC-SHA-512/224 (RFC 2104) on ARMv7

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/Arm.lean`). `init` sets both states' hash values with
SHA-512/224's verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad`
word by word into their buffers, and absorbs each with one call of
SHA-512/224's verified compression function.

`finalize` finalizes the inner state with SHA-512/224's verified streaming
`finalize`, then computes the outer hash as one call of SHA-512's verified
compression function (`vg_sha512_compress`), on a block laid out at fixed
offsets in `scratch`. It pushes 8 bytes of stack (the stack arguments of
`finalize`); `stack` is that of the shared contract, 16 bytes.

`init` and `finalize` keep their working space in a frame of their own
(`Proof/Pbkdf2/Md/Arm/Frame.lean`); `init_scratch` and `finalize_scratch`, the
same code with it as an argument, are what PBKDF2's code calls.
-/

namespace VG.Artifacts.HmacSha512_224.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.sha512_224I.initApi with
    target := Arm.target
    doc := Spec.Hmac.sha512_224I.initApi.doc
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_224I) 0 Proof.Pbkdf2.Md.Arm.sha512_224Md.hmacInit
    contract := Spec.Hmac.sha512_224I.initContract Arm.abi (16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_224I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_224I
    verified := Proof.Pbkdf2.Md.Arm.initFramed Proof.Pbkdf2.Md.Arm.Instances.sha512_224_init (by decide)
      Proof.Pbkdf2.Md.Arm.sha512_224_initFrameSat
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.sha512_224I.finalizeApi with
    target := Arm.target
    doc := Spec.Hmac.sha512_224I.finalizeApi.doc
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_224I) 1 Proof.Pbkdf2.Md.Arm.sha512_224Md.hmacFin
    contract := Spec.Hmac.sha512_224I.finalizeContract Arm.abi (16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_224I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_224I
    verified := Proof.Pbkdf2.Md.Arm.finFramed Proof.Pbkdf2.Md.Arm.Instances.sha512_224_finalize (by decide)
      Proof.Hmac.sha512_224_local (by decide) Proof.Pbkdf2.Md.Arm.sha512_224_finFrameSat
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.sha512_224I.initScratchApi with
    target := Arm.target
    doc := Spec.Hmac.sha512_224I.initScratchApi.doc
    code := Proof.Pbkdf2.Md.Arm.sha512_224Md.hmacInit
    contract := Spec.Hmac.sha512_224I.initScratchContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initScratchContract; rfl⟩
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha512_224_init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.sha512_224I.finalizeScratchApi with
    target := Arm.target
    doc := Spec.Hmac.sha512_224I.finalizeScratchApi.doc
    code := Proof.Pbkdf2.Md.Arm.sha512_224Md.hmacFin
    contract := Spec.Hmac.sha512_224I.finalizeScratchContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeScratchContract; rfl⟩
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha512_224_finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.HmacSha512_224.Arm
