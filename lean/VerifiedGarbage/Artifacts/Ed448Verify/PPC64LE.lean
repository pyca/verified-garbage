module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.VerifyVerified
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
# Ed448 verification on PPC64LE

The signature and documentation come from the reviewed Ed448 API. The
reference computations' agreement with the specification
(`Proof/Ed448/Facts.lean`) is passed to the proof here, so that only registration files import it.
-/

@[expose] public section

namespace VG.Artifacts.Ed448Verify.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed448.verifyApi.artifact PPC64LE.target {
    notes := ["Uses baseline integer instructions. Returns 0 at once for a context of 256 bytes \
      or more. Otherwise writes the first ten bytes of dom4(0, C) into a frame of 304 bytes on \
      the stack, hashes them, the context, R, the public key and the message with \
      `vg_keccak_absorb_scratch`, `vg_keccak_pad_scratch` and `vg_keccak_squeeze_scratch` \
      (SHAKE256, with the Keccak state and the sponge functions' working space in `scratch`) \
      into the frame, reduces the hash modulo L there with `vg_ed448_scalar_reduce`, and \
      returns `vg_ed448_verify_equation`'s result. The saved nonvolatile registers and `lr` are \
      in the frame too, which is not cleared: verification has no secrets."]
    code := Impl.Ed448.PPC64LE.Whole.verifyCode
    stack := 352
    verified := Proof.Ed448.PPC64LE.Whole.verify_framed Proof.Ed448.recover_ok Proof.Ed448.verifyEq4_ok }]

end VG.Artifacts.Ed448Verify.PPC64LE
