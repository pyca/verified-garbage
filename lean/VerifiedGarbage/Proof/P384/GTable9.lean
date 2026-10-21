module

import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
public import VerifiedGarbage.Impl.P384.GTable9
public import VerifiedGarbage.Proof.Weierstrass.CombCheckW
public import VerifiedGarbage.Spec.P384

/-!
# P-384: the table of the verifier's generator digits is right

`p384G9` has the shape of a comb of one window of nine bits; `combChecksW`
checks its entries `[m]G`, `m = 1 … 256`, and its start `[256]G` against the
specification's group law, which the kernel evaluates once (`gtabChecks9_p384`),
giving the facts the verifier's generator row needs (`gtabOk9`).
-/

@[expose] public section

namespace VG.Proof.P384

open Spec.Weierstrass Weierstrass

theorem gtabChecks9_p384 : combChecksW Spec.P384.curve.p Spec.P384.curve.a
    (Spec.P384.curve.gx, Spec.P384.curve.gy) (2 ^ (9 - 1)) 1 Impl.P384.p384G9 [Impl.P384.p384G9Start]
    Impl.P384.p384G9Start = true :=
  -- By walking the table (`combChecksF`) rather than indexing it.
  combChecksW_of_fast (by decide +kernel)

theorem gtabOk9 (hL : Law Spec.P384.curve) :
    CombOkW Spec.P384.curve 9 1 Impl.P384.p384G9 Impl.P384.p384G9Start :=
  combOkW_of_check hL onCurve_G (by decide) gtabChecks9_p384

end VG.Proof.P384
