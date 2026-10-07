import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Verified
import VerifiedGarbage.Proof.Ed448.AArch64.BaseVerified

/-!
# Ed448 signing with a cached public key on AArch64

A generic file (see `TCB/Emit.lean`): `vg_ed448_sign_cached` calls the SHA-3
sponge functions with an implementation `v` of the Keccak permutation
(`Variants/Keccak/AArch64/`), so it is emitted once for each implementation,
named with its suffix, and needs its CPU features. The signature and
documentation come from the reviewed Ed448 API. The correctness of
`vg_ed448_scalar_base` (`Proof/Ed448/AArch64/BaseVerified.lean`) is passed to
the proof here, so that only registration and generic files import its algebra.
-/

namespace VG.Generic.Keccak.AArch64.Ed448SignCached

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  { Spec.Ed448.signCachedApi with
    name := Spec.Ed448.signCachedApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.Ed448.signCachedApi.doc (notes := ["Uses baseline integer instructions, and \
      those of the Keccak permutation it calls. Hashes with `vg_keccak_absorb_scratch`, \
      `vg_keccak_pad_scratch` and `vg_keccak_squeeze_scratch` (SHAKE256, into its stack frame, \
      with the Keccak state and the sponge functions' working space in `scratch`): the private \
      key, whose first half, pruned, \
      is the secret scalar s, kept in the frame; then dom4(0, C), the prefix and the message, \
      reduced modulo L with `vg_ed448_scalar_reduce` into the second half of `out` (r); \
      R = [r]B with `vg_ed448_scalar_base` into the first half of `out`; then dom4(0, C), R, \
      the public key and the message, reduced into the frame (k); and \
      S = (r + k s) mod L with `vg_ed448_scalar_mul_add` over r. Clears the frame's hash, k \
      and s; the callees' working values are left in `scratch`. The function saves `x30` and \
      its arguments on the stack, and the functions it calls use 16 bytes below its frame."])
    consts := Impl.X448.AArch64.Base.combConsts
    code := Impl.Ed448.AArch64.SignCached.signCachedWith v.callee
    contract := Spec.Ed448.signCachedContract (AArch64.abi.withConsts Impl.X448.AArch64.Base.combConsts) 352
    stack := 352
    verified := Proof.Ed448.AArch64.SignCached.signCached_verified v Proof.Ed448.AArch64.scalarBase_baseOk
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.Keccak.AArch64.Ed448SignCached
