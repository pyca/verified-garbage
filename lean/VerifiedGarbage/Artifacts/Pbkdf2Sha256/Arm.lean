import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Frame

/-!
# PBKDF2-HMAC-SHA-256 (RFC 8018) on ARMv7: the iteration and the whole derivation

The iteration is the one for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/Arm.lean`): each step is two calls of SHA-256's verified
compression function (`vg_sha256_compress`), on blocks laid out once at fixed
offsets in `scratch`. It uses no stack; `stack` is that of the shared
contract, 16 bytes.

The whole derivation, `pbkdf2`, is the one for every streaming hash function
(`Impl/Pbkdf2/Whole/Arm.lean`), calling the hash function's streaming
functions, HMAC's `init` and `finalize` and the iteration above. `stack` is
that of the shared contract, 24 bytes: `pbkdf2` pushes `update`'s 16 bytes of
stack arguments, or 8 bytes around a call of a function that uses 16. It
runs in a frame holding its working space
(`Proof.Pbkdf2.Whole.Arm.pbkFramed`).
-/

namespace VG.Artifacts.Pbkdf2Sha256.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.sha256I.iterateApi with
    target := Arm.target
    doc := Spec.Hmac.sha256I.iterateApi.doc
    code := Proof.Pbkdf2.Md.Arm.sha256Md.iterate
    contract := Spec.Hmac.sha256I.iterateContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha256_iterate
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.sha256I.pbkdf2Api with
    target := Arm.target
    doc := Spec.Hmac.sha256I.pbkdf2Api.doc
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Whole.Arm.pbkFrame Spec.Hmac.sha256I) 3
      Proof.Pbkdf2.Whole.Arm.sha256F.pbkdf2
    contract := Spec.Hmac.sha256I.pbkdf2Contract Arm.abi (24 + Proof.Pbkdf2.Whole.Arm.pbkFrame Spec.Hmac.sha256I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.pbkdf2Contract Spec.Pbkdf2.pbkdf2Contract; rfl⟩
    stack := 24 + Proof.Pbkdf2.Whole.Arm.pbkFrame Spec.Hmac.sha256I
    verified := Proof.Pbkdf2.Whole.Arm.pbkFramed Proof.Pbkdf2.Whole.Arm.sha256 (by decide)
      Proof.Pbkdf2.Whole.Arm.sha256_pbkFrameSat
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  -- Scrypt's code calls `pbkdf2` with its own working space.
  { Spec.Hmac.sha256I.pbkdf2ScratchApi with
    target := Arm.target
    doc := Spec.Hmac.sha256I.pbkdf2ScratchApi.doc
    code := Proof.Pbkdf2.Whole.Arm.sha256F.pbkdf2
    contract := Spec.Hmac.sha256I.pbkdf2ScratchContract Arm.abi 24
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.pbkdf2ScratchContract; rfl⟩
    stack := 24
    verified := Proof.Pbkdf2.Whole.Arm.sha256
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Pbkdf2Sha256.Arm
