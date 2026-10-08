import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sha256.Arm.Shared

/-!
# SHA-224 (FIPS 180-4) on ARMv7

SHA-224 is SHA-256 from another initial hash value, and its digest the first
28 bytes of the final hash value: its `init` and its `finalize`, which writes
its digest, are its own, and it continues with SHA-256's `update`
(`Artifacts/Sha256/`).
-/

namespace VG.Artifacts.Sha224.Arm

def artifacts : List Artifact := [
  { Spec.Sha256.init224Api with
    target := Arm.target
    doc := Spec.Sha256.init224Api.doc
    code := Impl.Sha256.Arm.Stream.init224
    contract := Spec.Sha256.init224Contract Arm.abi
    verified := Proof.Sha256.Arm.Shared.init224
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha256.finalize224Api with
    target := Arm.target
    doc := Spec.Sha256.finalize224Api.doc
    code := Impl.StackScratch.Arm.withStackScratch 624 1 Impl.Sha256.Arm.Stream.finalize224
    contract := Spec.Sha256.finalize224Contract Arm.abi 624
    stack := 624
    verified := Proof.Sha256.Arm.Shared.finalize224
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha224.Arm
