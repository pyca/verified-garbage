module

public import VerifiedGarbage.Proof.Ecdh.X86_64.BrainpoolP256r1.CheckVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # brainpoolP256r1's check of a public point on x86-64 -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.X86_64.CheckPointBrainpoolP256r1

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64.BrainpoolP256r1.Check

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP256r1.curve) : List Artifact :=
  [false].map fun adx =>
    C.checkApi.artifact X86_64.target {
      suffix := (if adx then "_adx" else "")
      code := code adx
      verified := verified h.inv adx
      features := if adx then ["bmi2", "adx"] else [] }

end VG.Generic.BrainpoolP256r1.X86_64.CheckPointBrainpoolP256r1
