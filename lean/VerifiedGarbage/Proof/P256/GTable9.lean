module

import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
public import VerifiedGarbage.Impl.P256.GTable9
public import VerifiedGarbage.Proof.Weierstrass.CombCheckW
public import VerifiedGarbage.Spec.P256

/-!
# P-256: the table of the verifier's generator digits is right

`p256G9` has the shape of a comb of one window of nine bits; `combChecksW`
checks its entries `[m]G`, `m = 1 … 256`, and its start `[256]G` against the
specification's group law, which the kernel evaluates once (`gtabChecks9_p256`),
giving the facts the verifier's generator row needs (`gtabOk9`).
-/

@[expose] public section

namespace VG.Proof.P256

open Spec.Weierstrass Weierstrass

theorem gtabChecks9_p256 : combChecksW Spec.P256.curve.p Spec.P256.curve.a
    (Spec.P256.curve.gx, Spec.P256.curve.gy) (2 ^ (9 - 1)) 1 Impl.P256.p256G9 [Impl.P256.p256G9Start]
    Impl.P256.p256G9Start = true :=
  -- By walking the table (`combChecksF`) rather than indexing it.
  combChecksW_of_fast (by decide +kernel)

theorem gtabOk9 (hL : Law Spec.P256.curve) :
    CombOkW Spec.P256.curve 9 1 Impl.P256.p256G9 Impl.P256.p256G9Start :=
  combOkW_of_check hL onCurve_G (by decide) gtabChecks9_p256

end VG.Proof.P256
