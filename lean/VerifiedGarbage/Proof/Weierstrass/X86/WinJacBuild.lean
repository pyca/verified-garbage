import VerifiedGarbage.Proof.Weierstrass.X86.WinJacCoZInit
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacCoZStep

/-! Construct all sixteen cached multiples for the secret-scalar window. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem build_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    (hn : 17≤C.n) {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity)
    {s : State} (hI : Inv K.M base size C.p (·∈slots K) (ro K) (tmv C K.M.n base s) s)
    (hJ : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) (hz : tmv C K.M.n base s K.P.z=1) :
    WP isa K.build s (BuildInv K C base size wk P s 16) := by
  unfold JacWinCfg.build
  apply WP.seq
  refine WP.mono (build_init_ok hL hW hI hJ hz hC) fun a ia => ?_
  have jp : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y) 1 P := by
    simpa only [hz] using hJ
  apply WP.assoc
  apply WP.assoc
  apply WP.seq
  refine WP.mono (WP.assoc' (co_init_ok hL hW hm hC ha hO hn hP hP0 ia hI.lt jp hz)) fun b ib => ?_
  refine WP.loop (M:=isa)
    (fun j t => 1≤j ∧ j≤14 ∧ CoBuildInv K C base size wk P s (16-j) t)
    (fun j u ⟨hj,hj14,hu⟩ => ?_) 14 b ⟨by decide,by decide,ib⟩
  refine WP.mono (co_step_ok hL hW hm hC ha hO hn hP hP0 (by omega) (by omega) hu hI.lt)
    fun t ⟨it,zt⟩ => ?_
  by_cases he : j=1
  · subst j
    refine Or.inl ⟨?_,it.inv⟩
    change Option.map Bool.not t.zf=some false
    rw [zt]; rfl
  · refine Or.inr ⟨?_,j-1,by omega,by omega,by omega,?_⟩
    · change Option.map Bool.not t.zf=some true
      rw [zt,decide_eq_false (by omega)]
      rfl
    · rw [show 16-(j-1)=16-j+1 from by omega]
      exact it

end VG.Proof.Weierstrass.X86.JWin
