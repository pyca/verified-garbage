import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Sha224
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Frame

/-!
# HMAC-SHA-224 (RFC 2104) on ARMv7

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/Arm.lean`). `init` sets both states' hash values with
SHA-224's verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` word
by word into their buffers, and absorbs each with one call of SHA-256's
verified compression function (`vg_sha256_compress`).

`finalize` finalizes the inner state with SHA-256's verified streaming
`finalize`, then computes the outer hash as one call of SHA-256's verified
compression function (`vg_sha256_compress`), on a block laid out at fixed
offsets in `scratch`. It pushes 8 bytes of stack (the stack arguments of
`finalize`); `stack` is that of the shared contract, 16 bytes.

`init` and `finalize` keep their working space in a frame of their own
(`Proof/Pbkdf2/Md/Arm/Frame.lean`); `init_scratch` and `finalize_scratch`, the
same code with it as an argument, are what PBKDF2's code calls.
-/

namespace VG.Artifacts.HmacSha224.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.sha224I.initApi with
    target := Arm.target
    doc := Spec.Hmac.sha224I.initApi.doc
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha224I) 0 Proof.Pbkdf2.Md.Arm.sha224Md.hmacInit
    contract := Spec.Hmac.sha224I.initContract Arm.abi (16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha224I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha224I
    verified := Proof.Pbkdf2.Md.Arm.initFramed Proof.Pbkdf2.Md.Arm.Instances.sha224_init (by decide)
      Proof.Pbkdf2.Md.Arm.sha224_initFrameSat
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.sha224I.finalizeApi with
    target := Arm.target
    doc := Spec.Hmac.sha224I.finalizeApi.doc
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha224I) 1 Proof.Pbkdf2.Md.Arm.sha224Md.hmacFin
    contract := Spec.Hmac.sha224I.finalizeContract Arm.abi (16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha224I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha224I
    verified := Proof.Pbkdf2.Md.Arm.finFramed Proof.Pbkdf2.Md.Arm.Instances.sha224_finalize (by decide)
      Proof.Hmac.sha224_local (by decide) Proof.Pbkdf2.Md.Arm.sha224_finFrameSat
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.sha224I.initScratchApi with
    target := Arm.target
    doc := Spec.Hmac.sha224I.initScratchApi.doc
    code := Proof.Pbkdf2.Md.Arm.sha224Md.hmacInit
    contract := Spec.Hmac.sha224I.initScratchContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initScratchContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha224_init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.sha224I.finalizeScratchApi with
    target := Arm.target
    doc := Spec.Hmac.sha224I.finalizeScratchApi.doc
    code := Proof.Pbkdf2.Md.Arm.sha224Md.hmacFin
    contract := Spec.Hmac.sha224I.finalizeScratchContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeScratchContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha224_finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.HmacSha224.Arm
