import VerifiedGarbage.Proof.Weierstrass.X86.NafDigit
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! One counted iteration of the public Jacobian multiplication. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

structure NafLoopKeep (K : WinCfg) (base : Addr) (wk : Nat) (s t : State) : Prop where
  keep : Keeps (clob++[.esi]) s t
  mem : Unch base (progW K.M wk (winOther K)) s.mem t.mem

theorem NafLoopKeep.refl (K : WinCfg) (base : Addr) (wk : Nat) (s : State) :
    NafLoopKeep K base wk s s := ⟨Keeps.refl _ _,Unch.refl _ _ _⟩

theorem NafLoopKeep.trans {K : WinCfg} {base : Addr} {wk : Nat} {s t u : State}
    (h : NafLoopKeep K base wk s t) (h' : NafLoopKeep K base wk t u) :
    NafLoopKeep K base wk s u := ⟨h.keep.trans h'.keep,fun x hx => (h'.mem x hx).trans (h.mem x hx)⟩

theorem nafStep_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk k j : Nat}
    (hL : NafLay K size) (hJ : K.J=65) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hj : j<256) {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : NafCore K C base size P (Naf5.byte k) (Naf5.residual k (j+1)) s)
    (hc : s.gpr .esi=BitVec.ofNat 32 (j+1)) :
    WP isa (Naf.windowStep K F) s fun t => NafLoopKeep K base wk s t ∧
      NafCore K C base size P (Naf5.byte k) (Naf5.residual k j) t ∧
      t.gpr .esi=BitVec.ofNat 32 j ∧ t.zf=some (decide (j=0)) := by
  rw [Naf.windowStep]
  apply WP.seq
  refine wp_decCounter (by omega) hc fun a ca ka ma => WP.block_nil ?_
  have cka : CKeeps [.esi] s a := ⟨ka.1,ma,ka.2⟩
  have ia := h.of_keeps cka (by decide)
  apply WP.assoc
  apply WP.seq
  refine WP.mono (nafDoubleCore_ok hL hAcc hBitsWk hJ hm hC ha hP ia) fun b ⟨kb,ib⟩ => ?_
  have cb : b.gpr .esi=BitVec.ofNat 32 j := by
    rw [kb.gpr _ (by decide),ca,Nat.add_sub_cancel]
  apply WP.seq
  refine WP.mono (nafDigit_ok hL hJ hAcc hBitsWk hm hC ha hOne (by omega) hP ib cb)
    fun c ⟨kc,ic⟩ => ?_
  have cc : c.gpr .esi=BitVec.ofNat 32 j := (kc.gpr _ (by decide)).trans cb
  refine wp_testCounter (by omega) cc fun t ft zt => WP.block_nil ?_
  have kt : CKeeps [] c t := ⟨fun r _ => congrFun ft.gpr r,ft.mem,ft.rd,ft.wr⟩
  have kp := kb.trans kc
  refine ⟨⟨?_,?_⟩,ic.of_keeps kt (by decide),(congrFun ft.gpr .esi).trans cc,zt⟩
  · exact (ka.mono (fun _ hr => List.mem_append_right _ hr)).trans
      ((Keeps.mono ⟨kp.gpr,kp.rd,kp.wr⟩ (fun _ hr => List.mem_append_left _ hr)).trans
        (kt.keeps.mono (by simp)))
  · rw [ft.mem]
    simpa only [ma] using kp.unch

end VG.Proof.Weierstrass.X86
