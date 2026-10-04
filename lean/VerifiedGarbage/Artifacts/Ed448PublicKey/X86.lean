import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Ed448.X86.PublicKey.Verified
import VerifiedGarbage.Proof.Ed448.X86.BaseVerified
import VerifiedGarbage.Proof.Ed448.X86.BaseLit
import VerifiedGarbage.Proof.Ed448.Facts

/-!
# Ed448 public-key derivation on x86 (32-bit)

The signature and documentation come from the reviewed Ed448 API. The proof
of `vg_ed448_scalar_base` is passed to the caller's here, so that only this
file imports it, with the reference ladder's agreement with the
specification (`Proof/Ed448/Facts.lean`).
-/

namespace VG.Artifacts.Ed448PublicKey.X86

open VG.X86

theorem base_ok : Proof.Ed448.X86.CalleeOk Proof.Ed448.X86.scalarBaseLocal Impl.Ed448.X86.scalarBase :=
  ⟨Proof.Ed448.X86.scalarBase_ok Proof.Ed448.baseLadder_ok, Proof.Ed448.X86.scalarBase_ct,
    NoSp.of_all (by lit_decide), by lit_decide⟩

def artifacts : List Artifact := [
  { Spec.Ed448.publicKeyApi with
    target := X86.target
    doc := Spec.Ed448.publicKeyApi.doc (notes := ["Uses baseline integer instructions. \
      Hashes the private key with `vg_keccak_absorb_scratch`, `vg_keccak_pad_scratch` and \
      `vg_keccak_squeeze_scratch` (SHAKE256, the Keccak state in `scratch`) into a stack frame, \
      prunes the first 57 bytes of the hash there, encodes `[s]B` with \
      `vg_ed448_scalar_base`, and clears the frame, the hash and the scalar with it, \
      before returning. The Keccak state, and the base-point multiplication's working \
      values, are left in `scratch`."])
    code := Impl.Ed448.X86.PublicKey.code Impl.Ed448.X86.scalarBase
    contract := Spec.Ed448.publicKeyContract X86.abi 280
    stack := 280
    verified := Proof.Ed448.X86.PublicKey.publicKey_verified base_ok
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed448PublicKey.X86
