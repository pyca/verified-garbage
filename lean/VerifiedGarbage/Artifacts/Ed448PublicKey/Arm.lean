module

public import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Verified
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
# Ed448 public-key derivation on ARMv7

The signature and documentation come from the reviewed Ed448 API. The
reference ladder's agreement with the specification (`Proof/Ed448/Facts.lean`)
is passed to the proof here, so that only registration files import it.
-/

@[expose] public section

namespace VG.Artifacts.Ed448PublicKey.Arm

def artifacts : List Artifact := [
  Spec.Ed448.publicKeyApi.artifact Arm.target {
    notes := ["Uses baseline integer instructions. \
      Hashes the private key with `vg_keccak_absorb_scratch`, `vg_keccak_pad_scratch` and \
      `vg_keccak_squeeze_scratch` (SHAKE256, the Keccak state in `scratch`) into a stack frame, \
      prunes the first 57 bytes of the hash there, encodes `[s]B` with \
      `vg_ed448_scalar_base`, and clears the frame, the hash and the scalar with it, \
      before returning. The Keccak state, and the base-point multiplication's working \
      values, are left in `scratch`."]
    code := Impl.Ed448.Arm.PublicKey.code
    stack := 280
    verified := Proof.Ed448.Arm.PublicKey.publicKey_verified Proof.Ed448.baseLadder_ok }]

end VG.Artifacts.Ed448PublicKey.Arm
