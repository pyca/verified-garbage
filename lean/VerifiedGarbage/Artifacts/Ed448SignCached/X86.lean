module

public import VerifiedGarbage.Proof.Ed448.X86.ScalarBaseOk
public import VerifiedGarbage.Proof.Ed448.X86.SignCached.Verified
import VerifiedGarbage.Proof.Sha3.X86.Lit
import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 signing with a cached public key on x86 (32-bit)

The signature and documentation come from the reviewed Ed448 API. The proof
of `vg_ed448_scalar_base` is passed to the caller's here, so that only this
file imports it, with the reference ladder's agreement with the
specification (`Proof/Ed448/Facts.lean`).
-/

@[expose] public section

namespace VG.Artifacts.Ed448SignCached.X86

open VG.X86

def artifacts : List Artifact := [
  Spec.Ed448.signCachedApi.artifact X86.target {
    notes := ["Uses baseline integer instructions. Hashes with \
      `vg_keccak_absorb_scratch`, `vg_keccak_pad_scratch` and `vg_keccak_squeeze_scratch` (SHAKE256, \
      into its stack frame, with the Keccak state and the sponge functions' working space in \
      `scratch`): the private key, whose first half, pruned in place, is the secret scalar s; \
      then dom4(0, C), the prefix and the message, reduced modulo L with \
      `vg_ed448_scalar_reduce` into the second half of `out` (r); R = [r]B with \
      `vg_ed448_scalar_base` into the first half of `out`; then dom4(0, C), R, the public key \
      and the message, reduced into the frame (k); and S = (r + k s) mod L with \
      `vg_ed448_scalar_mul_add` over r. Clears the frame, the hash, s and k with it, before \
      returning; the callees' working values are left in `scratch`."]
    code := Impl.Ed448.X86.SignCached.code Impl.Ed448.X86.scalarBase
    stack := 280
    verified := Proof.Ed448.X86.SignCached.signCached_verified Proof.Ed448.X86.scalarBase_calleeOk }]

end VG.Artifacts.Ed448SignCached.X86
