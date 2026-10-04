import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Instances
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Frame

/-!
# HMAC-MD5 (RFC 2104) on ARMv7

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/Arm.lean`). `init` sets both states' hash values with MD5's
verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` word by word
into their buffers, and absorbs each with one call of MD5's verified
compression function.

`finalize` finalizes the inner state with MD5's verified streaming `finalize`,
then computes the outer hash as one call of MD5's verified compression
function (`vg_md5_compress`), on a block laid out at fixed offsets in
`scratch`. It pushes 8 bytes of stack (the stack arguments of `finalize`);
`stack` is that of the shared contract, 16 bytes.

`init` and `finalize` keep their working space in a frame of their own
(`Proof/Pbkdf2/Md/Arm/Frame.lean`); `init_scratch` and `finalize_scratch`, the
same code with it as an argument, are what PBKDF2's code calls.
-/

namespace VG.Artifacts.HmacMd5.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.md5I.initApi with
    target := Arm.target
    doc := Spec.Hmac.md5I.initApi.doc
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.md5I) 0 Proof.Pbkdf2.Md.Arm.md5Md.hmacInit
    contract := Spec.Hmac.md5I.initContract Arm.abi (16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.md5I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.md5I
    verified := Proof.Pbkdf2.Md.Arm.initFramed Proof.Pbkdf2.Md.Arm.Instances.md5_init (by decide)
      Proof.Pbkdf2.Md.Arm.md5_initFrameSat
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.md5I.finalizeApi with
    target := Arm.target
    doc := Spec.Hmac.md5I.finalizeApi.doc
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.md5I) 1 Proof.Pbkdf2.Md.Arm.md5Md.hmacFin
    contract := Spec.Hmac.md5I.finalizeContract Arm.abi (16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.md5I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.md5I
    verified := Proof.Pbkdf2.Md.Arm.finFramed Proof.Pbkdf2.Md.Arm.Instances.md5_finalize (by decide)
      Proof.Hmac.md5_local (by decide) Proof.Pbkdf2.Md.Arm.md5_finFrameSat
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.md5I.initScratchApi with
    target := Arm.target
    doc := Spec.Hmac.md5I.initScratchApi.doc
    code := Proof.Pbkdf2.Md.Arm.md5Md.hmacInit
    contract := Spec.Hmac.md5I.initScratchContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initScratchContract; rfl⟩
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.md5_init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.md5I.finalizeScratchApi with
    target := Arm.target
    doc := Spec.Hmac.md5I.finalizeScratchApi.doc
    code := Proof.Pbkdf2.Md.Arm.md5Md.hmacFin
    contract := Spec.Hmac.md5I.finalizeScratchContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeScratchContract; rfl⟩
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.md5_finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.HmacMd5.Arm
