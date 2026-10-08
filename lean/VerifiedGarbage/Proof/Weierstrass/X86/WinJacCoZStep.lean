import VerifiedGarbage.Proof.Weierstrass.X86.WinJacCoZAdd
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacCoZStore
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacCounter

/-! One public shared-Z table-construction iteration. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem co_step_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk m : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    (hn : 17≤C.n) {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity)
    (h2 : 2≤m) (h15 : m≤15) {s₀ s : State} (h : CoBuildInv K C base size wk P s₀ m s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p) :
    WP isa K.buildStep s fun t => CoBuildInv K C base size wk P s₀ (m+1) t ∧
      t.zf=some (decide (m+1=16)) := by
  unfold JacWinCfg.buildStep
  apply WP.seq
  refine WP.mono (inc_counter_ok h.inv.counter) fun a ⟨ca,ka⟩ => ?_
  have fa := h.inv.frame.keeps ka
  have pa := h.inv.point.congr (p:=fun c => K.T+32*c) fun _ _ => by rw [ka.2.1]
  have da := h.shared.keeps ka
  have ia := fa.inv_cached hL hW hro pa
  have ia' : Inv K.M base size C.p (·∈slots K) (K.D.x::K.D.y::live K)
      (tmv C K.M.n base a) a := by
    refine ⟨ia.scr,ia.mod,?_,?_,fun _ _ => rfl⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|rfl|hx
      · simp [slots,work]
      · simp [slots,work]
      · exact ia.sl x hx
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|rfl|hx
      · exact da.lt _ (by simp)
      · exact da.lt _ (by simp)
      · exact ia.lt x hx
  have ja : InvJ C (tmv C K.M.n base a K.E.x) (tmv C K.M.n base a K.E.y)
      (tmv C K.M.n base a K.E.z) (mul m P) := by
    simpa only [hL.n,JacWinCfg.E,Nat.reduceMul,Nat.add_zero] using pa.jac
  have za : tmv C K.M.n base a K.E.z≠0 := by
    simpa only [hL.n,JacWinCfg.E,Nat.reduceMul] using pa.z
  have z2a : tmv C K.M.n base a K.z2=tmv C K.M.n base a K.E.z*tmv C K.M.n base a K.E.z := by
    simpa only [hL.n,JacWinCfg.E,JacWinCfg.z2,Nat.reduceMul] using pa.z2
  apply WP.seq
  refine WP.mono (zaddu_point_ok hL hW hm hC ha hO hn hP hP0 h2 h15 ia'
    (by intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [live]) da.point ja za z2a)
    fun b ⟨kb,pb,db⟩ => ?_
  have fb := fa.field hL hW kb (fun _ hx => hx)
  have ta : Table K C base P m a := fun i h1 hm => (h.inv.table i h1 hm).congr fun _ _ => by rw [ka.2.1]
  have tb := ta.field_keep hL fa.scr kb (fun _ hx => hx) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (co_store_ok hL hW fb (by omega) ((kb.gpr _ (by decide)).trans ca) tb pb db)
    fun c hc => ?_
  refine WP.mono (cmp_counter_ok (by omega) hc.inv.counter) fun t ⟨zt,kt,ct⟩ => ?_
  refine ⟨⟨⟨hc.inv.frame.keeps kt,?_,?_,ct⟩,hc.shared.keeps kt⟩,zt⟩
  · intro i h1 hm
    exact (hc.inv.table i h1 hm).congr fun _ _ => by rw [kt.2.1]
  · exact hc.inv.point.congr fun _ _ => by rw [kt.2.1]

end VG.Proof.Weierstrass.X86.JWin
