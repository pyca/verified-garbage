module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.PublicKeyVerified
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
# Ed448 public-key derivation on PPC64LE

The signature and documentation come from the reviewed Ed448 API. The
reference ladder's agreement with the specification (`Proof/Ed448/Facts.lean`) is passed to the proof here, so that only registration files import it.
-/

@[expose] public section

namespace VG.Artifacts.Ed448PublicKey.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed448.publicKeyApi.artifact PPC64LE.target {
    notes := ["Uses baseline integer instructions. Hashes the private key with \
      `vg_keccak_absorb_scratch`, `vg_keccak_pad_scratch` and `vg_keccak_squeeze_scratch` \
      (SHAKE256, the Keccak state and the sponge functions' working space in `scratch`) into a \
      frame of 192 bytes on the stack, prunes the first 57 bytes of the hash there, and encodes \
      `[s]B` with `vg_ed448_scalar_base`. The hash, the scalar, the saved nonvolatile registers \
      and `lr` are in the frame, whose first 120 bytes are cleared before returning; the Keccak \
      state, and the base-point multiplication's working values, are left in `scratch`."]
    code := Impl.Ed448.PPC64LE.Whole.publicKeyCode
    stack := 240
    verified := Proof.Ed448.PPC64LE.Whole.publicKey_framed Proof.Ed448.baseLadder2_ok }]

end VG.Artifacts.Ed448PublicKey.PPC64LE
