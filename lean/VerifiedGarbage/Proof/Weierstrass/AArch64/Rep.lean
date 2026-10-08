import VerifiedGarbage.Proof.Weierstrass.AArch64.Ladder
import VerifiedGarbage.Proof.Weierstrass.Law

/-!
# Short Weierstrass curves on AArch64: the ladder computes `[k]P`

The invariant of the group law for `ladder_ok`: `R` represents `[k >>> j]P`,
for the point `P` that `G` represents, which an iteration keeps
(`step_rep`, by `ladder_step`) when the slots of `a` and `3b` hold the
curve's.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass Spec.Weierstrass

theorem step_rep {L : LadderCfg} {C : Curve} {base : Addr} {s : State} {k : Nat} {P : Point C}
    (hC : Law C) (hP : onCurve C P = true)
    (ha : tmv C L.M.n base s L.S.a = Fin.ofNat C.p C.a)
    (hb : tmv C L.M.n base s L.S.b3 = Fin.ofNat C.p (3 * C.b))
    (hG : Rep C (tmv C L.M.n base s L.G.x) (tmv C L.M.n base s L.G.y) (tmv C L.M.n base s L.G.z) P) :
    Step L C base s k fun j X Y Z => Rep C X Y Z (mul (k >>> j) P) := by
  intro j _ X Y Z X2 Y2 Z2 X3 Y3 Z3 hQ h2 h3
  rw [ha, hb] at h2 h3
  exact ladder_step hC hP hG hQ h2 h3

end VG.Proof.Weierstrass.AArch64
