module

public import VerifiedGarbage.Proof.Ecdh.X86_64.BrainpoolP384r1.CheckVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # brainpoolP384r1's check of a public point on x86-64 -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.X86_64.CheckPointBrainpoolP384r1

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64.BrainpoolP384r1.Check

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP384r1.curve) : List Artifact :=
  [C.checkApi.artifact X86_64.target {
      code := code
      verified := verified h.inv }]

end VG.Generic.BrainpoolP384r1.X86_64.CheckPointBrainpoolP384r1
