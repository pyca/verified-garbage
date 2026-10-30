module

public import VerifiedGarbage.Proof.Ecdh.AArch64.P224.CheckVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-224's check of a public point on AArch64

`vg_p224_check_point` (`Spec/Weierstrass/CheckPoint.lean`), which P-224's ECDH and
signature verification call to check the public point. A generic file (see
`TCB/Emit.lean`) over P-224's group law and inversions `h`, the variant
`Variants/P224/AArch64/Law.lean`, whose inversions' soundness the proof of the
configuration takes.
-/

@[expose] public section

namespace VG.Generic.P224.AArch64.CheckPointP224

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64.P224.Check

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P224.curve) : List Artifact := [
  C.checkApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Cfg.checkFn p224
    verified := verified h.inv }]

end VG.Generic.P224.AArch64.CheckPointP224
