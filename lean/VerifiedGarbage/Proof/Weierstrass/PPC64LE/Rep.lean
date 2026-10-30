module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.LadderP
public import VerifiedGarbage.Proof.Weierstrass.Law

/-!
# Short Weierstrass curves on PPC64LE: the ladder computes `[k]P`

The invariant of the group law for `ladderP_ok`: `R` represents
`[k >>> j]P`, for the point `P` that `G` represents, which an iteration keeps
(`step_rep`, by `ladder_step`) when the slots of `a` and `3b` hold the
curve's, as on 32-bit ARM (`Proof/Weierstrass/Arm/Rep.lean`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Weierstrass VG.Spec.Weierstrass VG.Proof.Weierstrass

theorem step_rep' {L : LadderCfg} {C : Curve} {base : Addr} {s : State} {k : Nat} {P : Point C}
    (hC : Law C) (hP : onCurve C P = true)
    (ha : tmv C L.M.n base s L.S.a = Fin.ofNat C.p C.a)
    (hb : tmv C L.M.n base s L.S.b3 = Fin.ofNat C.p (3 * C.b))
    (hG : Rep C (tmv C L.M.n base s L.G.x) (tmv C L.M.n base s L.G.y) (tmv C L.M.n base s L.G.z) P)
    {a0 : Bool} (h0 : a0 = true → (Fin.ofNat C.p C.a : Fe C) = 0 ∧ tmv C L.M.n base s L.G.z = 1) :
    Step L C base s k (fun j X Y Z => Rep C X Y Z (mul (k >>> j) P)) a0 := by
  intro j _ X Y Z X2 Y2 Z2 X3 Y3 Z3 hQ h2 h3
  rw [ha, hb] at h2 h3
  exact ladder_step' hC hP h0 hG hQ h2 h3

theorem step_rep {L : LadderCfg} {C : Curve} {base : Addr} {s : State} {k : Nat} {P : Point C}
    (hC : Law C) (hP : onCurve C P = true)
    (ha : tmv C L.M.n base s L.S.a = Fin.ofNat C.p C.a)
    (hb : tmv C L.M.n base s L.S.b3 = Fin.ofNat C.p (3 * C.b))
    (hG : Rep C (tmv C L.M.n base s L.G.x) (tmv C L.M.n base s L.G.y) (tmv C L.M.n base s L.G.z) P) :
    Step L C base s k fun j X Y Z => Rep C X Y Z (mul (k >>> j) P) :=
  step_rep' hC hP ha hb hG nofun

end VG.Proof.Weierstrass.PPC64LE.Point
