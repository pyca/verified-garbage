module

import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Ecdh.AArch64.P521.CheckVerified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

/-!
# P-521's check of a public point on AArch64

`vg_p521_check_point` (`Spec/Weierstrass/CheckPoint.lean`), which P-521's ECDH and
signature verification call to check the public point. A generic file (see
`TCB/Emit.lean`) over P-521's group law and inversions `h`, the variant
`Variants/P521/AArch64/Law.lean`, whose inversions' soundness the proof of the
configuration takes.
-/

@[expose] public section

namespace VG.Generic.P521.AArch64.CheckPointP521

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64.P521.Check

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P521.curve) : List Artifact := [
  { C.checkApi with
    target := AArch64.target
    doc := C.checkApi.doc (notes := ["The function compares `x` and `y` with `p` by chains of \
      subtractions with borrow (`subs`, `sbcs`), multiplies them by `R² mod p` by calls of the curve's Montgomery multiplication function (`Spec/Weierstrass/Mont.lean`), computes \
      `y² - (x³ + a x + b)` by the same products and additions and subtractions modulo `p`, \
      ANDs the masks of the comparisons and of that number being zero into the flag, and \
      selects the point by masks; nothing depends on the numbers but through masks. It keeps `x21`–`x25` in lanes of `v24`–`v26` while it runs."])
    code := Impl.Ecdh.AArch64.Cfg.checkFn p521
    contract := C.checkContract AArch64.abi
    verified := verified h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P521.AArch64.CheckPointP521
