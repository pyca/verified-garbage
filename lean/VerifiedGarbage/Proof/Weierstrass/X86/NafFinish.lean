import VerifiedGarbage.Proof.Weierstrass.X86.NafWindow
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJOut

/-! One final conversion from Jacobian to homogeneous coordinates. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafFinish_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk e : Nat}
    {β : Nat → BitVec 8} (hL : NafLay K size)
    (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (hOne : K.one<C.p)
    (hOneM : toM C.p (2^(64*K.M.n)) K.one=1)
    {P : Point C} {s : State} (h : NafCore K C base size P β e s) :
    WP isa (Naf.finish K F) s fun t =>
      ProgKeep K.M base wk (winOther K) s t ∧ ModOkW K.M size C.p t.mem base ∧
      (∀ x∈jacCoords K.R,wordsVal t.mem base x K.M.n<C.p) ∧
      Rep C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y)
        (tmv C K.M.n base t K.R.z) (mul e P) := by
  have wr : ∀ x∈jacCoords K.R,x∈winOther K := by
    intro x hx; simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have sl := fun x hx => nafOther_slots K x (wr x hx)
  have lt := fun x hx => h.field.lt x (nafLive_R K x hx)
  have hn := hL.nodup
  simp only [winOther,rcbW,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
    List.not_mem_nil,or_false,not_or] at hn
  have hxy : K.R.x≠K.R.y := by grind
  have hzy : K.R.z≠K.R.y := by grind
  have hpn := wordsVal_lt s.mem base K.M.mo K.M.n
  rw [h.field.mod.val] at hpn
  have hzero : K.zero∈nafSlots K := nafRo_slots K _ (by simp [winRo])
  have hy0 := hL.lay.apart K.R.y K.zero (sl _ (by simp [jacCoords])) hzero
    (fun he => hL.ro K.zero (by simp [winRo]) (he ▸ wr _ (by simp [jacCoords])))
  unfold Naf.finish
  apply WP.seq
  refine WP.mono (outFix_ok (VG.Impl.Weierstrass.X86.WinCfg.tc K F) h.field.scr (by change 1≤K.M.n; rw [hL.n]; decide)
    (Nat.lt_trans hOne hpn) (hL.lay.le _ (sl K.R.y (by simp [jacCoords])))
    (hL.lay.le _ (sl K.R.z (by simp [jacCoords]))) (hL.lay.le _ hzero) hy0 h.stable.zero)
    fun a ⟨ya,ka,oa⟩ => ?_
  simp only [VG.Impl.Weierstrass.X86.WinCfg.tc] at ya oa
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
  have ia : Inv K.M base size C.p (·∈nafSlots K) (jacCoords K.R) E a :=
    (h.field.update hL.lay hAcc (sl _ (by simp [jacCoords])) pa la ey).sub
      (fun x hx => List.mem_cons_of_mem _ (nafLive_R K x hx))
  have opsSl : ∀ op∈(VG.Impl.Weierstrass.X86.WinCfg.tc K F).outOps,∀ x∈op.out::op.ins,x∈nafSlots K := by
    intro op hop x hx
    apply nafOther_slots K x
    simp only [TCombCfg.outOps,VG.Impl.Weierstrass.X86.WinCfg.tc,List.mem_cons,List.not_mem_nil,or_false] at hop
    rcases hop with rfl|rfl|rfl <;>
      simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx <;>
      rcases hx with rfl|rfl|rfl <;> simp [winOther,rcbW]
  refine WP.mono (fprog_ok hL.lay hAcc hm (VG.Impl.Weierstrass.X86.WinCfg.tc K F).outOps ia opsSl
    (by simp [readsOk,TCombCfg.outOps,VG.Impl.Weierstrass.X86.WinCfg.tc,jacCoords,FOp.ins,FOp.out])) fun t ⟨pt,it⟩ => ?_
  have vr : ∀ x∈jacCoords K.R,x∈validAfter (VG.Impl.Weierstrass.X86.WinCfg.tc K F).outOps (jacCoords K.R) :=
    fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
  refine ⟨(pa.mono (by intro x hx; rw [List.mem_singleton.mp hx]; exact wr _ (by simp [jacCoords]))).trans
    (pt.mono (by
      intro x hx
      simp only [TCombCfg.outOps,VG.Impl.Weierstrass.X86.WinCfg.tc,FOp.out,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> simp [winOther,rcbW])),it.mod,fun x hx => it.lt x (vr x hx),?_⟩
  have ev : ∀ x∈jacCoords K.R,tmv C K.M.n base t x=runOps (VG.Impl.Weierstrass.X86.WinCfg.tc K F).outOps E x :=
    fun x hx => it.val x (vr x hx)
  rw [ev _ (by simp [jacCoords]),ev _ (by simp [jacCoords]),ev _ (by simp [jacCoords])]
  have hxt : K.R.x≠K.S.t0 := by grind
  have hzt : K.R.z≠K.S.t0 := by grind
  have hxz : K.R.x≠K.R.z := by grind
  have hyt : K.R.y≠K.S.t0 := by grind
  simp only [TCombCfg.outOps,VG.Impl.Weierstrass.X86.WinCfg.tc,runOps,List.foldl_cons,List.foldl_nil,FOp.run,Function.update_apply,
    hxt,hzt,hxz,hyt,hzy.symm,hxz.symm,hxt.symm,hxy.symm,ite_true,ite_false]
  simp only [E,Function.update_of_ne hxy,Function.update_of_ne hzy,Function.update_self]
  exact InvJ.out hC h.point

end VG.Proof.Weierstrass.X86
