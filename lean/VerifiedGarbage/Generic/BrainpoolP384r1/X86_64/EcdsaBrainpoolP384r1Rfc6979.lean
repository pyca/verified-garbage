module

import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP384r1Any
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over brainpoolP384r1 with any hash function on x86-64

A generic file (see `TCB/Emit.lean`) over brainpoolP384r1's group law and inversions
`h`, the variant `Variants/BrainpoolP384r1/X86_64/Law.lean`: `vg_ecdsa_brainpoolp384r1_rfc6979_sign`,
calling the streaming functions of the hash function `hash` names through
the table `hash_fns`, which the caller chooses, and `vg_ecdsa_brainpoolp384r1_sign`.

The stack is 408 bytes: a 384-byte frame, and the 24 bytes below it that the
calls use (a streaming function's return address and the 8 bytes it may use
below it; `vg_ecdsa_brainpoolp384r1_sign` only its return address).
-/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.X86_64.EcdsaBrainpoolP384r1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.X86_64 (anyNotes)
open VG.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP384r1Any (any verified)

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst.signAnyApi.artifact X86_64.target {
    notes := [anyNotes Spec.Ecdsa.BrainpoolP384r1.signApi.name]
    code := (any h.law h.inv).code
    stack := 408
    verified := verified h.law h.inv
    spSafe := (any h.law h.inv).any_spSafe }]

end VG.Generic.BrainpoolP384r1.X86_64.EcdsaBrainpoolP384r1Rfc6979
