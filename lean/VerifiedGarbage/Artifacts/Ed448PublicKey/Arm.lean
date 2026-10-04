import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Verified
import VerifiedGarbage.Proof.Ed448.Facts

/-!
# Ed448 public-key derivation on ARMv7

The signature and documentation come from the reviewed Ed448 API. The
reference ladder's agreement with the specification (`Proof/Ed448/Facts.lean`)
is passed to the proof here, so that only registration files import it.
-/

namespace VG.Artifacts.Ed448PublicKey.Arm

def artifacts : List Artifact := [
  { Spec.Ed448.publicKeyApi with
    target := Arm.target
    doc := Spec.Ed448.publicKeyApi.doc (notes := ["Uses baseline integer instructions. \
      Hashes the private key with `vg_keccak_absorb`, `vg_keccak_pad` and \
      `vg_keccak_squeeze` (SHAKE256, the Keccak state in `scratch`) into a stack frame, \
      prunes the first 57 bytes of the hash there, encodes `[s]B` with \
      `vg_ed448_scalar_base`, and clears the frame, the hash and the scalar with it, \
      before returning. The Keccak state, and the base-point multiplication's working \
      values, are left in `scratch`."])
    code := Impl.Ed448.Arm.PublicKey.code
    contract := Spec.Ed448.publicKeyContract Arm.abi 280
    stack := 280
    verified := Proof.Ed448.Arm.PublicKey.publicKey_verified Proof.Ed448.baseLadder_ok
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed448PublicKey.Arm
