import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed448.Arm.SignCached.Verified
import VerifiedGarbage.Proof.Ed448.Facts

/-!
# Ed448 signing with a cached public key on ARMv7

The signature and documentation come from the reviewed Ed448 API. The
reference ladder's agreement with the specification (`Proof/Ed448/Facts.lean`)
is passed to the proof here, so that only registration files import it.
-/

namespace VG.Artifacts.Ed448SignCached.Arm

def artifacts : List Artifact := [
  { Spec.Ed448.signCachedApi with
    target := Arm.target
    doc := Spec.Ed448.signCachedApi.doc (notes := ["Uses baseline integer instructions. Hashes with \
      `vg_keccak_absorb_scratch`, `vg_keccak_pad_scratch` and `vg_keccak_squeeze_scratch` (SHAKE256, \
      into its stack frame, with the Keccak state and the sponge functions' working space in \
      `scratch`): the private key, whose first half, pruned in place, is the secret scalar s; \
      then dom4(0, C), the prefix and the message, reduced modulo L with \
      `vg_ed448_scalar_reduce` into the second half of `out` (r); R = [r]B with \
      `vg_ed448_scalar_base` into the first half of `out`; then dom4(0, C), R, the public key \
      and the message, reduced into the frame (k); and S = (r + k s) mod L with \
      `vg_ed448_scalar_mul_add` over r. Clears the frame, the hash, s and k with it, before \
      returning; the callees' working values are left in `scratch`."])
    code := Impl.Ed448.Arm.SignCached.code
    contract := Spec.Ed448.signCachedContract Arm.abi 280
    stack := 280
    verified := Proof.Ed448.Arm.SignCached.signCached_verified Proof.Ed448.baseLadder_ok
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed448SignCached.Arm
