module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Ecdh.AArch64.P256.CheckVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-256's check of a public point on AArch64

`vg_p256_check_point` (`Spec/Weierstrass/CheckPoint.lean`), which P-256's ECDH and
signature verification call to check the public point. A generic file (see
`TCB/Emit.lean`) over P-256's group law and inversions `h`, the variant
`Variants/P256/AArch64/Law.lean`, whose inversions' soundness the proof of the
configuration takes.
-/

@[expose] public section

namespace VG.Generic.P256.AArch64.CheckPointP256

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64.P256.Check

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvToMOrd Spec.P256.curve) : List Artifact := [
  C.checkApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Cfg.checkFn p256
    verified := verified h.inv }]

end VG.Generic.P256.AArch64.CheckPointP256
