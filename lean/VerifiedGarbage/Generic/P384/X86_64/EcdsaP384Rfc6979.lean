module

import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.P384.Comb7
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P384Any
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over P-384 with any hash function on x86-64

A generic file (see `TCB/Emit.lean`) over P-384's group law and inversions
`h`, the variant `Variants/P384/X86_64/Law.lean`: `vg_ecdsa_p384_rfc6979_sign`,
calling the streaming functions of the hash function `hash` names through
the table `hash_fns`, which the caller chooses, and `vg_ecdsa_p384_sign`. It is emitted for each multiplication of `vg_ecdsa_p384_sign`: the baseline's, and BMI2's and ADX's (`vg_ecdsa_p384_rfc6979_sign_adx`, calling `vg_ecdsa_p384_sign_adx`).

The stack is 408 bytes: a 384-byte frame, and the 24 bytes below it that the
calls use (a streaming function's return address and the 8 bytes it may use
below it; `vg_ecdsa_p384_sign` only its return address).

It reads the comb's tables of `vg_ecdsa_p384_sign`.
-/

@[expose] public section

namespace VG.Generic.P384.X86_64.EcdsaP384Rfc6979

open VG.Proof.Ecdsa.Rfc6979.X86_64 (anyNotes)
open VG.Proof.Ecdsa.Rfc6979.X86_64.P384Any (any verified)

/-- The signature with P-384's multiplication with BMI2 and ADX (`adx`, `_adx`,
calling `vg_ecdsa_p384_sign_adx`) or not. -/
def withMul (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P384.curve) (adx : Bool) : Artifact :=
  Spec.Ecdsa.Rfc6979.P384Sha384.inst.signAnyApi.artifact X86_64.target {
    suffix := if adx then "_adx" else ""
    notes := [anyNotes (Spec.Ecdsa.P384.signApi.name ++ (if adx then "_adx" else ""))]
    code := (any adx h.law (Proof.P384.combOk7 h.law) h.inv).code
    consts := Impl.Ecdsa.X86_64.p384.combConsts
    stack := 408
    verified := verified adx h.law (Proof.P384.combOk7 h.law) h.inv
    spSafe := (any adx h.law (Proof.P384.combOk7 h.law) h.inv).any_spSafe
    features := if adx then ["bmi2", "adx", "avx", "avx2"] else [] }

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P384.curve) : List Artifact :=
  [withMul h false, withMul h true]

end VG.Generic.P384.X86_64.EcdsaP384Rfc6979
