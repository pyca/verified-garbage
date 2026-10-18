module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.P224.Comb7
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P224Any
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over P-224 with any hash function on x86-64

A generic file (see `TCB/Emit.lean`) over P-224's group law and inversions
`h`, the variant `Variants/P224/X86_64/Law.lean`: `vg_ecdsa_p224_rfc6979_sign`,
calling the streaming functions of the hash function `hash` names through
the table `hash_fns`, which the caller chooses, and `vg_ecdsa_p224_sign`.

The stack is 408 bytes: a 384-byte frame, and the 24 bytes below it that the
calls use (a streaming function's return address and the 8 bytes it may use
below it; `vg_ecdsa_p224_sign` only its return address).

It reads the comb's tables of `vg_ecdsa_p224_sign`.
-/

@[expose] public section

namespace VG.Generic.P224.X86_64.EcdsaP224Rfc6979

open VG.Proof.Ecdsa.Rfc6979.X86_64 (anyNotes)
open VG.Proof.Ecdsa.Rfc6979.X86_64.P224Any (any verified)

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P224.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P224Sha224.inst.signAnyApi.artifact X86_64.target {
    notes := [anyNotes Spec.Ecdsa.P224.signApi.name]
    code := (any h.law (Proof.P224.combOk7 h.law) h.inv).code
    consts := Impl.Ecdsa.X86_64.p224.combConsts
    stack := 408
    verified := verified h.law (Proof.P224.combOk7 h.law) h.inv
    spSafe := (any h.law (Proof.P224.combOk7 h.law) h.inv).any_spSafe }]

end VG.Generic.P224.X86_64.EcdsaP224Rfc6979
