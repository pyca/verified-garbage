import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Weierstrass.JacAdd

/-! The two branchless selections make each nonexceptional window addition total. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG Spec.Weierstrass

def addResult {C : Curve} (a : Nat) (R E : Fe C × Fe C × Fe C) : Fe C × Fe C × Fe C :=
  if a=0 then R else if R.2.2=0 then E else jacAddF R.1 R.2.1 R.2.2 E.1 E.2.1 E.2.2

theorem winPt_ne {C : Curve} (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P=true)
    (hP0 : P≠.infinity) (hn : 17≤C.n) {v j : Nat} (ha : magH 16 (Window5.nib v j)≠0) :
    Window5.winPt C P v j≠.infinity := by
  have hb : magH 16 (Window5.nib v j)≤16 := magH_le (Nat.mod_lt _ (by decide))
  have hm := Window5.mul_ne_infinity hO hP hP0 (by omega : 1≤magH 16 (Window5.nib v j)) (by omega)
  rw [Window5.winPt_mag]
  split
  · cases hp : mul (magH 16 (Window5.nib v j)) P with
    | infinity => exact False.elim (hm hp)
    | affine x y => intro he; cases he
  · exact hm

theorem add_result_ok {C : Curve} (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity)
    (hn17 : C.n%32=17) (hn64 : 64≤C.n) {k J j : Nat} (hk : k<C.n) (hj : j<J)
    {R E : Fe C × Fe C × Fe C}
    (hR : InvJ C R.1 R.2.1 R.2.2 (mul (32*Window5.winE (k+16*Window5.geom J) J (j+1)) P))
    (hE : InvJ C E.1 E.2.1 E.2.2 (Window5.winPt C P (k+16*Window5.geom J) j)) :
    let t := addResult (magH 16 (Window5.nib (k+16*Window5.geom J) j)) R E
    InvJ C t.1 t.2.1 t.2.2 (mul (Window5.winE (k+16*Window5.geom J) J j) P) := by
  have he := Window5.win_add hC hP (k:=k+16*Window5.geom J) (Nat.le_add_left _ _) hj
  dsimp only [addResult]
  split
  next hz =>
    rw [Window5.winPt_zero hz] at he
    have he' : mul (32*Window5.winE (k+16*Window5.geom J) J (j+1)) P =
        mul (Window5.winE (k+16*Window5.geom J) J j) P := by
      cases hp : mul (32*Window5.winE (k+16*Window5.geom J) J (j+1)) P <;>
        simpa only [hp,Spec.Weierstrass.add] using he
    rw [←he']; exact hR
  next hz =>
    split
    next rz =>
      rw [(hR.z_zero_iff hC).mp rz] at he
      rw [←he]; exact hE
    next rz =>
      have ez : E.2.2≠0 := fun he => winPt_ne hO hP hP0 (by omega) hz ((hE.z_zero_iff hC).mp he)
      have he1 : 1≤Window5.winE (k+16*Window5.geom J) J (j+1) := by
        by_contra he1
        have he0 : Window5.winE (k+16*Window5.geom J) J (j+1)=0 := by omega
        apply rz
        apply (hR.z_zero_iff hC).mpr
        rw [he0,Nat.mul_zero,Window5.mul_zero_pt]
      have noexc := Window5.loop_noexc hC hO hP hP0 hn17 hn64 hk hj he1
      have hp := hC.onCurve_mul hP (32*Window5.winE (k+16*Window5.geom J) J (j+1))
      have hq := Window5.onCurve_winPt hC hP (k+16*Window5.geom J) j
      have hh : E.1*(R.2.2*R.2.2)-R.1*(E.2.2*E.2.2)≠0 := by
        intro hh
        by_cases hy : E.2.1*R.2.2*(R.2.2*R.2.2)-R.2.1*E.2.2*(E.2.2*E.2.2)=0
        · exact noexc.1 (hR.same hC hE rz ez hh hy)
        · exact noexc.2 (hR.opposite hC hp hq hE rz ez hh hy)
      rw [←he]
      exact hR.add_ne hC ha hp hq hE rz ez hh

end VG.Proof.Weierstrass.X86.JWin
