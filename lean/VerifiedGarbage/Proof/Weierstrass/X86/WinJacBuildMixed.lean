import VerifiedGarbage.Proof.Weierstrass.X86.WinJacBuildDouble
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacMixed

/-! The finite mixed addition used for entries three through sixteen. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem mixed_work (K : JacWinCfg) :
    ∀ x∈rcbW K.S K.E++[K.z2,K.z3],x∈work K := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact rcb_E_work K x hx
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> simp [work]

theorem mixed_nd {K : JacWinCfg} {size wk : Nat} (hL : Layout K size wk) :
    ([K.S.t0,K.S.t1,K.S.t2,K.S.t3,K.S.t4,K.S.t5,K.E.x,K.E.y,K.E.z,K.z2,K.z3] : List Nat).Nodup := by
  apply List.Nodup.sublist (l₂:=work K) _ hL.nd
  simp only [work,temps,List.cons_append,List.nil_append]
  repeat first | exact List.Sublist.refl _ | apply List.Sublist.cons_cons | apply List.Sublist.cons

theorem mixed_point_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (·∈slots K) V E s)
    (hV : ∀ x∈[K.S.t2,K.S.t4,K.E.x,K.E.y,K.E.z,K.P.x,K.P.y],x∈V)
    (h2 : E K.S.t2=E K.E.x) (h4 : E K.S.t4=E K.E.y)
    {P Q : Point C} (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hJ : InvJ C (E K.E.x) (E K.E.y) (E K.E.z) Q)
    (hA : InvJ C (E K.P.x) (E K.P.y) 1 P) (hz : E K.E.z≠0)
    (hne : Q≠P) (hinf : Spec.Weierstrass.add Q P≠.infinity) :
    WP isa (fprog K.F (K.maddOps++K.cacheOps)) s fun t =>
      Cached C base t (fun c => K.T+32*c) (Spec.Weierstrass.add Q P) ∧
      ProgKeep K.M base wk (rcbW K.S K.E++[K.z2,K.z3]) s t := by
  have hp : ∀ x∈[K.P.x,K.P.y,K.P.z],x∉[K.S.t0,K.S.t1,K.S.t2,K.S.t3,K.S.t4,K.S.t5,K.E.x,K.E.y,K.E.z,K.z2,K.z3] := by
    intro x hx hw
    apply hL.readonly x ?_ (mixed_work K x hw)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [ro]
  have hall : ∀ x∈[K.S.t0,K.S.t1,K.S.t2,K.S.t3,K.S.t4,K.S.t5,K.E.x,K.E.y,K.E.z,K.z2,K.z3]++
      [K.P.x,K.P.y,K.P.z],x∈slots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact List.mem_append_right _ (mixed_work K x hx)
    · apply List.mem_append_left
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> simp [ro]
  refine WP.mono (maddCache_ok hL.lay hW hm (mixed_nd hL) hp hall hI hV h2 h4)
    fun t ⟨kt,e,it,et,e2,e3⟩ => ⟨?_,kt⟩
  have hh : E K.P.x*(E K.E.z*E K.E.z)-E K.E.x*(1*1)≠0 := by
    intro he
    by_cases hy : E K.P.y*E K.E.z*(E K.E.z*E K.E.z)-E K.E.y*1*(1*1)=0
    · exact hne (hJ.same hC hA hz hC.one_ne_zero he hy)
    · exact hinf (hJ.opposite hC hQ hP hA hz hC.one_ne_zero he hy)
  have hj := hJ.add_ne hC ha hQ hP hA hz hC.one_ne_zero hh
  have je : InvJ C (e K.E.x) (e K.E.y) (e K.E.z) (Spec.Weierstrass.add Q P) := by
    change (fun j : Fe C × Fe C × Fe C => InvJ C j.1 j.2.1 j.2.2 (Spec.Weierstrass.add Q P))
      (e K.E.x,e K.E.y,e K.E.z)
    rw [et]
    exact hj
  apply Cached.of_inv hL.n it _ je (fun hz => hinf ((je.z_zero_iff hC).mp hz)) e2 e3
  intro c hc
  have : c=0 ∨ c=1 ∨ c=2 ∨ c=3 ∨ c=4 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl <;> simp [JacWinCfg.E,JacWinCfg.z2,JacWinCfg.z3]

end VG.Proof.Weierstrass.X86.JWin
