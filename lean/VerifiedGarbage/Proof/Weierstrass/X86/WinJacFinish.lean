import VerifiedGarbage.Proof.Weierstrass.X86.WinJacAccum
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJOut

/-! One final conversion from Jacobian to homogeneous coordinates. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem finish_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k e : Nat}
    (hL : Layout K size wk) (hAcc : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (hOne : K.one<C.p)
    (hOneM : toM C.p (2^(64*K.M.n)) K.one=1)
    {P : Point C} {s₀ s : State} (h : Accum K C base size wk P k s₀ e s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hz : wordsVal s₀.mem base K.zero K.M.n=0) :
    WP isa K.finish s fun t =>
      ProgKeep K.M base wk (work K) s t ∧ ModOkW K.M size C.p t.mem base ∧
      (∀ x∈jacCoords K.R,wordsVal t.mem base x K.M.n<C.p) ∧
      (k<C.n → Rep C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y)
        (tmv C K.M.n base t K.R.z) (mul e P)) := by
  have hi := h.inv hL hAcc hro
  have vr0 : ∀ x∈jacCoords K.R,x∈ro K++[K.R.x,K.R.y,K.R.z] := fun _ hx => List.mem_append_right _ hx
  have zero : wordsVal s.mem base K.zero K.M.n=0 := by
    rw [h.frame.ro hL hAcc (by simp [ro])]; exact hz
  have wr : ∀ x∈jacCoords K.R,x∈work K := by
    intro x hx; simp only [jacCoords,work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have sl : ∀ x∈jacCoords K.R,x∈slots K := fun x hx => List.mem_append_right _ (wr x hx)
  have lt := fun x hx => hi.lt x (vr0 x hx)
  have hn := hL.nd
  simp only [work,temps,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
    List.not_mem_nil,or_false,not_or] at hn
  have hxy : K.R.x≠K.R.y := by grind
  have hzy : K.R.z≠K.R.y := by grind
  have hpn := wordsVal_lt s.mem base K.M.mo K.M.n
  rw [hi.mod.val] at hpn
  have hzero : K.zero∈slots K := List.mem_append_left _ (by simp [ro])
  have hy0 := hL.lay.apart K.R.y K.zero (sl _ (by simp [jacCoords])) hzero
    (fun he => hL.readonly K.zero (by simp [ro]) (he ▸ wr _ (by simp [jacCoords])))
  unfold JacWinCfg.finish
  apply WP.seq
  refine WP.mono (outFix_ok K.tc hi.scr (by change 1≤K.M.n; rw [hL.n]; decide)
    (Nat.lt_trans hOne hpn) (hL.lay.le _ (sl K.R.y (by simp [jacCoords])))
    (hL.lay.le _ (sl K.R.z (by simp [jacCoords]))) (hL.lay.le _ hzero) hy0 zero)
    fun a ⟨ya,ka,oa⟩ => ?_
  simp only [JacWinCfg.tc] at ya oa
  have pa : ProgKeep K.M base wk [K.R.y] s a :=
    ⟨fun r hr => ka.gpr r (fun he => hr (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl|rfl <;> simp [clob])),ka.rd,ka.wr,
      Outs.of_outside oa (by simp [progW])⟩
  have la : wordsVal a.mem base K.R.y K.M.n<C.p := by
    rw [ya]
    by_cases hz : wordsVal s.mem base K.R.z K.M.n=0
    · simpa only [hz,↓reduceIte] using hOne
    · simpa only [hz,↓reduceIte] using lt K.R.y (by simp [jacCoords])
  have ey : toM C.p (2^(64*K.M.n)) (wordsVal a.mem base K.R.y K.M.n)=
      if tmv C K.M.n base s K.R.z=0 then 1 else tmv C K.M.n base s K.R.y := by
    rw [ya]
    by_cases hz : wordsVal s.mem base K.R.z K.M.n=0
    · have hz' : tmv C K.M.n base s K.R.z=0 := by unfold tmv; rw [hz,toM_zero]
      simp only [hz,hz',↓reduceIte]; exact hOneM
    · have hz' : tmv C K.M.n base s K.R.z≠0 := fun he =>
        hz ((toM_eq_zero_iff hm (lt _ (by simp [jacCoords]))).mp he)
      simp only [hz,hz',↓reduceIte]
  let E := Function.update (tmv C K.M.n base s) K.R.y
    (if tmv C K.M.n base s K.R.z=0 then 1 else tmv C K.M.n base s K.R.y)
  have ia : Inv K.M base size C.p (·∈slots K) (jacCoords K.R) E a :=
    (hi.update hL.lay hAcc (sl _ (by simp [jacCoords])) pa la ey).sub
      (fun x hx => List.mem_cons_of_mem _ (vr0 x hx))
  have opsSl : ∀ op∈K.tc.outOps,∀ x∈op.out::op.ins,x∈slots K := by
    intro op hop x hx
    apply List.mem_append_right
    simp only [TCombCfg.outOps,JacWinCfg.tc,List.mem_cons,List.not_mem_nil,or_false] at hop
    rcases hop with rfl|rfl|rfl <;>
      simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx <;>
      rcases hx with rfl|rfl|rfl <;> simp [work,temps]
  refine WP.mono (fprog_ok hL.lay hAcc hm K.tc.outOps ia opsSl
    (by simp [readsOk,TCombCfg.outOps,JacWinCfg.tc,jacCoords,FOp.ins,FOp.out])) fun t ⟨pt,it⟩ => ?_
  have vr : ∀ x∈jacCoords K.R,x∈validAfter K.tc.outOps (jacCoords K.R) :=
    fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
  refine ⟨(pa.mono (by intro x hx; rw [List.mem_singleton.mp hx]; exact wr _ (by simp [jacCoords]))).trans
    (pt.mono (by
      intro x hx
      simp only [TCombCfg.outOps,JacWinCfg.tc,FOp.out,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> simp [work,temps])),it.mod,fun x hx => it.lt x (vr x hx),?_⟩
  intro hk
  have ev : ∀ x∈jacCoords K.R,tmv C K.M.n base t x=runOps K.tc.outOps E x :=
    fun x hx => it.val x (vr x hx)
  rw [ev _ (by simp [jacCoords]),ev _ (by simp [jacCoords]),ev _ (by simp [jacCoords])]
  have hxt : K.R.x≠K.S.t0 := by grind
  have hzt : K.R.z≠K.S.t0 := by grind
  have hxz : K.R.x≠K.R.z := by grind
  have hyt : K.R.y≠K.S.t0 := by grind
  simp only [TCombCfg.outOps,JacWinCfg.tc,runOps,List.foldl_cons,List.foldl_nil,FOp.run,Function.update_apply,
    hxt,hzt,hxz,hyt,hzy.symm,hxz.symm,hxt.symm,hxy.symm,ite_true,ite_false]
  simp only [E,Function.update_of_ne hxy,Function.update_of_ne hzy,Function.update_self]
  exact InvJ.out hC (h.point hk)

end VG.Proof.Weierstrass.X86.JWin
