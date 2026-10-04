import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed448.AArch64.PublicKey.Verified
import VerifiedGarbage.Proof.Ed448.Facts

/-!
# Ed448 public-key derivation on AArch64

A generic file (see `TCB/Emit.lean`): `vg_ed448_public_key` calls the SHA-3
sponge functions with an implementation `v` of the Keccak permutation
(`Variants/Keccak/AArch64/`), so it is emitted once for each implementation,
named with its suffix, and needs its CPU features. The signature and
documentation come from the reviewed Ed448 API. The reference ladder's
agreement with the specification (`Proof/Ed448/Facts.lean`) is passed to the
proof here, so that only registration and generic files import it.
-/

namespace VG.Generic.Keccak.AArch64.Ed448PublicKey

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  { Spec.Ed448.publicKeyApi with
    name := Spec.Ed448.publicKeyApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.Ed448.publicKeyApi.doc (notes := ["Uses baseline integer instructions, and \
      those of the Keccak permutation it calls. Hashes the private key with \
      `vg_keccak_absorb_scratch`, `vg_keccak_pad_scratch` and `vg_keccak_squeeze_scratch` \
      (SHAKE256, into its stack frame, with the Keccak state in `scratch`), prunes the first 57 \
      bytes of the hash into the frame, encodes `[s]B` \
      with `vg_ed448_scalar_base`, and clears the frame's scalar and hash. The base-point \
      multiplication's working values are left in `scratch`. The function saves `x30` and its \
      arguments on the stack, and the functions it calls use 16 bytes below its frame."])
    code := Impl.Ed448.AArch64.PublicKey.publicKeyWith v.callee
    contract := Spec.Ed448.publicKeyContract AArch64.abi 352
    stack := 352
    verified := Proof.Ed448.AArch64.PublicKey.publicKey_verified v Proof.Ed448.baseLadder_ok
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.Keccak.AArch64.Ed448PublicKey
