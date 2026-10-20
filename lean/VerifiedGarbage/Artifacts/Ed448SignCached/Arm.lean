module

public import VerifiedGarbage.Proof.Ed448.Arm.SignCached.Verified
public import VerifiedGarbage.Proof.Ed448.Facts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 signing with a cached public key on ARMv7

The signature and documentation come from the reviewed Ed448 API. The
reference ladder's agreement with the specification (`Proof/Ed448/Facts.lean`)
is passed to the proof here, so that only registration files import it.
-/

@[expose] public section

namespace VG.Artifacts.Ed448SignCached.Arm

def artifacts : List Artifact := [
  Spec.Ed448.signCachedApi.artifact Arm.target {
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
    code := Impl.Ed448.Arm.SignCached.code
    stack := 280
    verified := Proof.Ed448.Arm.SignCached.signCached_verified Proof.Ed448.baseLadder_ok }]

end VG.Artifacts.Ed448SignCached.Arm
