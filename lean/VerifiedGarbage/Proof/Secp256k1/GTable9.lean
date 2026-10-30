module

import VerifiedGarbage.Proof.Secp256k1.Point
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
public import VerifiedGarbage.Impl.Secp256k1.GTable9
public import VerifiedGarbage.Proof.Weierstrass.CombCheckW
public import VerifiedGarbage.Spec.Secp256k1

/-!
# secp256k1: the table of the verifier's generator digits is right

`secp256k1G9` has the shape of a comb of one window of nine bits; `combChecksW`
checks its entries `[m]G`, `m = 1 … 256`, and its start `[256]G` against the
specification's group law, which the kernel evaluates once
(`gtabChecks9_secp256k1`), giving the facts the verifier's generator row needs (`gtabOk9`).
-/

@[expose] public section

namespace VG.Proof.Secp256k1

open Spec.Weierstrass Weierstrass

theorem gtabChecks9_secp256k1 : combChecksW Spec.Secp256k1.curve.p Spec.Secp256k1.curve.a
    (Spec.Secp256k1.curve.gx, Spec.Secp256k1.curve.gy) (2 ^ (9 - 1)) 1 Impl.Secp256k1.secp256k1G9
    [Impl.Secp256k1.secp256k1G9Start] Impl.Secp256k1.secp256k1G9Start = true :=
  -- By walking the table (`combChecksF`) rather than indexing it.
  combChecksW_of_fast (by decide +kernel)

theorem gtabOk9 (hL : Law Spec.Secp256k1.curve) :
    CombOkW Spec.Secp256k1.curve 9 1 Impl.Secp256k1.secp256k1G9 Impl.Secp256k1.secp256k1G9Start :=
  combOkW_of_check hL onCurve_G (by decide) gtabChecks9_secp256k1

end VG.Proof.Secp256k1
