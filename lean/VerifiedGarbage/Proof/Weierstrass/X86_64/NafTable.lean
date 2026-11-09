module
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableState
public import VerifiedGarbage.Proof.Weierstrass.JacMul

import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableInit
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableStep
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! Construction of the eight odd multiples used by the public verifier. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

/-- Build `P, 3P, …, 15P`, retaining the double in the ninth point, doubling by
any doubling of `C` (`JDblOk`). -/
theorem nafTable_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : NafLay K size) (hJ : 1≤K.J ∧ 4*K.J≤64*K.M.n+4)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) {dbl : RcbSlots → Pt → Pt → List FOp} (hd : JDblOk C dbl)
    (ht : K.tbl<2^31) (hOne : K.one<C.p) {P : Point C} (hP : onCurve C P=true)
    {s : State} (hI : Inv K.M base size C.p (·∈nafSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hJP : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) :
    WP isa (Naf.table K dbl).inline s (fun t => NafTableInv K C base size P s t 8) := by
  unfold Naf.table
  simp only [Code.inline]
  apply WP.assoc
  refine WP.seq (WP.mono (nafTable_init_ok hL hJ hm hC hd hP hI hJP) fun a ia => ?_)
  refine WP.loop (M:=isa)
    (fun j t => 1≤j ∧ j≤7 ∧ NafTableInv K C base size P s t (8-j))
    (fun j u ⟨hj,hj7,hu⟩ => ?_) 7 a ⟨by decide,by decide,ia⟩
  refine WP.mono (nafTable_step_ok hL hJ hm hC hd ht hOne hP (by omega) (by omega) hu)
    fun t ⟨it,cf⟩ => ?_
  by_cases hj1 : j=1
  · subst j
    exact Or.inl ⟨cf,it⟩
  · refine Or.inr ⟨?_,j-1,by omega,by omega,by omega,?_⟩
    · change t.cf=some true
      rw [cf]; congr 1; exact decide_eq_true (by omega)
    · rw [show 8-(j-1)=8-j+1 from by omega]
      exact it

end VG.Proof.Weierstrass.X86_64
