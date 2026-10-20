module

public import VerifiedGarbage.Proof.Ecdh.AArch64.BrainpoolP256r1.CheckVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# brainpoolP256r1's check of a public point on AArch64

`vg_brainpoolp256r1_check_point` (`Spec/Weierstrass/CheckPoint.lean`), which brainpoolP256r1's ECDH and
signature verification call to check the public point. A generic file (see
`TCB/Emit.lean`) over brainpoolP256r1's group law and inversions `h`, the variant
`Variants/BrainpoolP256r1/AArch64/Law.lean`, whose inversions' soundness the proof of the
configuration takes.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.AArch64.CheckPointBrainpoolP256r1

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64.BrainpoolP256r1.Check

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP256r1.curve) : List Artifact := [
  C.checkApi.artifact AArch64.target {
    notes := ["The function compares `x` and `y` with `p` by chains of \
      subtractions with borrow (`subs`, `sbcs`), multiplies them by `R² mod p` by word-by-word Montgomery multiplication (CIOS, with `mul` and `umulh`) inline, computes \
      `y² - (x³ + a x + b)` by the same products and additions and subtractions modulo `p`, \
      ANDs the masks of the comparisons and of that number being zero into the flag, and \
      selects the point by masks; nothing depends on the numbers but through masks."]
    code := Impl.Ecdh.AArch64.Cfg.checkFn brainpoolp256r1
    verified := verified h.inv }]

end VG.Generic.BrainpoolP256r1.AArch64.CheckPointBrainpoolP256r1
