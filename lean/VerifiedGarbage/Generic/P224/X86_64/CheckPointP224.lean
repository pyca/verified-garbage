module

public import VerifiedGarbage.Proof.Ecdh.X86_64.P224.CheckVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-224's check of a public point on x86-64

`vg_p224_check_point` (`Spec/Weierstrass/CheckPoint.lean`), which ECDH and
verification call. A generic file (see `TCB/Emit.lean`) over P-224's group law and inversions
`h`, the variant `Variants/P224/X86_64/Law.lean`, whose inversions'
soundness the proofs of the configuration take.
-/

@[expose] public section

namespace VG.Generic.P224.X86_64.CheckPointP224

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64.P224.Check

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P224.curve) : List Artifact :=
  [false].map fun adx =>
    C.checkApi.artifact X86_64.target {
      suffix := (if adx then "_adx" else "")
      code := code adx
      verified := verified h.inv adx
      features := if adx then ["bmi2", "adx"] else [] }

end VG.Generic.P224.X86_64.CheckPointP224
