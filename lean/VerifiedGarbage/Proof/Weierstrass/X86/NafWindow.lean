import VerifiedGarbage.Proof.Weierstrass.X86.NafWindowInit

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafWindow_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk k : Nat}
    (hL : NafLay K size) (hJ : K.J=65) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hk : k<2^256) {P : Point C} (hP : onCurve C P=true) {s : State}
    (hI : Inv K.M base size C.p (·∈nafSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hp : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P)
    (hz : wordsVal s.mem base K.zero K.M.n=0)
    (hb : ∀ i<257,s.mem (off base (K.bits+i))=Naf5.byte k i) :
    WP isa (Naf.window K F) s fun t =>
      KeepRegs (nafTableClob K) s t ∧ Unch base (nafTableWrites K wk) s.mem t.mem ∧
      NafCore K C base size P (Naf5.byte k) k t := by
  unfold Naf.window
  apply WP.assoc
  apply WP.seq
  refine WP.mono (nafWindow_init_ok hL hJ hAcc hBitsWk hm hC ha hOne hP hI hp hz hb)
    fun c ⟨kc,uc,cc,ci⟩ => ?_
  refine WP.mono (nafRun_ok hL hJ hAcc hBitsWk hm hC ha hOne hk hP cc ci)
    fun t ⟨kt,ct,_⟩ => ⟨kc.trans kt.keep,?_,ct⟩
  have ut : Unch base (nafTableWrites K wk) c.mem t.mem := kt.mem.mono (by
    intro w hw
    simp only [progW,nafTableWrites,nafWrites,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
    grind)
  exact (uc.trans ut).mono (by intro w hw; simpa only [List.mem_append,or_self] using hw)

end VG.Proof.Weierstrass.X86
