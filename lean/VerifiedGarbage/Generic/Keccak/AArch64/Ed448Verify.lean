import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Verified
import VerifiedGarbage.Proof.Ed448.Facts

/-!
# Ed448 verification on AArch64

A generic file (see `TCB/Emit.lean`): `vg_ed448_verify` calls the SHA-3
sponge functions with an implementation `v` of the Keccak permutation
(`Variants/Keccak/AArch64/`), so it is emitted once for each implementation,
named with its suffix, and needs its CPU features. The signature and
documentation come from the reviewed Ed448 API. The reference computations'
agreement with the specification (`Proof/Ed448/Facts.lean`) is passed to the
proof here, so that only registration and generic files import it.
-/

namespace VG.Generic.Keccak.AArch64.Ed448Verify

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  { Spec.Ed448.verifyApi with
    name := Spec.Ed448.verifyApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.Ed448.verifyApi.doc (notes := ["Uses baseline integer instructions, and \
      those of the Keccak permutation it calls. Returns 0 at once for a context of 256 bytes \
      or more. Otherwise writes the first ten bytes of dom4(0, C) into its stack frame, hashes \
      them, the context, R, the public key and the message with `vg_keccak_absorb`, \
      `vg_keccak_pad` and `vg_keccak_squeeze` (SHAKE256, with the Keccak state and the sponge \
      functions' working space in `scratch`) into the frame, reduces the hash modulo L there \
      with `vg_ed448_scalar_reduce`, and returns `vg_ed448_verify_equation`'s result. The \
      frame (the hash and k) is not cleared: verification has no secrets. The function saves \
      `x30` and its arguments on the stack, and the functions it calls use 16 bytes below its \
      frame."])
    code := Impl.Ed448.AArch64.Verify.verifyWith v.callee
    contract := Spec.Ed448.verifyContract AArch64.abi 352
    stack := 352
    verified := Proof.Ed448.AArch64.Verify.verify_verified v Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.Keccak.AArch64.Ed448Verify
