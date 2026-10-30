module

public import VerifiedGarbage.Proof.Ecdh.AArch64.P192.CheckVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-192's check of a public point on AArch64

`vg_p192_check_point` (`Spec/Weierstrass/CheckPoint.lean`), which P-192's ECDH and
signature verification call to check the public point. A generic file (see
`TCB/Emit.lean`) over P-192's group law and inversions `h`, the variant
`Variants/P192/AArch64/Law.lean`, whose inversions' soundness the proof of the
configuration takes.
-/

@[expose] public section

namespace VG.Generic.P192.AArch64.CheckPointP192

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64.P192.Check

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P192.curve) : List Artifact := [
  C.checkApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Cfg.checkFn p192
    verified := verified h.inv }]

end VG.Generic.P192.AArch64.CheckPointP192
