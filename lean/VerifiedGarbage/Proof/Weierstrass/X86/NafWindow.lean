import VerifiedGarbage.Proof.Weierstrass.X86.NafLoop

/-! Public multiplication from an affine input and its recoded scalar bytes. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafRun_initCounter_ok (s : State) :
    WP isa (.block [.mov .esi (.imm 256)]) s fun t => t.gpr .esi=256 ∧ CKeeps [.esi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,
    Option.map_some,RegUpd.gpr_setReg,ite_true,Option.some.injEq,exists_eq_left']
  exact ⟨trivial,fun r hr => by simp only [List.mem_singleton] at hr; simp only [RegUpd.gpr_setReg,hr,ite_false],rfl,rfl,rfl⟩

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
  have rr : ∀ x∈rcbW K.S K.R,x∈winOther K := by
    intro x hx; simp only [rcbW,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have rs : ∀ x∈jacCoords K.R,x∈nafSlots K := fun x hx =>
    nafOther_slots K x (rr x (by simp only [jacCoords,rcbW,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind))
  unfold Naf.window
  apply WP.seq
  refine WP.mono (nafTable_ok hL hAcc hJ hm hC ha hOne hP hI hp) fun a ia => ?_
  have za : wordsVal a.mem base K.zero K.M.n=0 := by
    rw [ia.unch.wordsVal (fun w hw => ?_) (by have := hL.lay.le K.zero (nafRo_slots K _ (by simp [winRo])); have := hI.scr.nowrap; omega),hz]
    simp only [nafTableWrites,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with ⟨x,hx,rfl⟩|rfl|rfl|rfl
    · exact hL.lay.apart K.zero x (nafRo_slots K _ (by simp [winRo])) (by
        simp only [nafWrites,nafSlots,List.mem_append] at hx ⊢; grind) (by
        intro he
        subst x
        simp only [nafWrites,List.mem_append] at hx
        rcases hx with hx|hx
        · exact hL.ro _ (by simp [winRo]) hx
        · have sep := hL.tbl K.zero (List.mem_append_left _ (by simp [winRo]))
          obtain ⟨i,hi,he⟩ := List.mem_map.mp hx
          have hi' := List.mem_range.mp hi
          rw [hL.n] at *
          omega)
    · exact hL.lay.tmp _ (nafRo_slots K _ (by simp [winRo]))
    · exact Or.inl (hAcc.sl _ (nafRo_slots K _ (by simp [winRo])))
    · have := hL.lay.le K.zero (nafRo_slots K _ (by simp [winRo]))
      have := hL.size_le
      dsimp only [Mont.outW]; omega
  have sa : NafStable K C base P (Naf5.byte k) a :=
    ⟨za,ia.table,ia.digits hL hBitsWk hb⟩
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (infinityPoint_ok hL.lay hAcc rs ia.field hOne) fun b ⟨eb,kb,ib,jb⟩ => ?_
  have cb : NafCore K C base size P (Naf5.byte k) 0 b :=
    ⟨(ib.sub (fun _ hx => List.mem_append_right _ hx)).to_tmv,
      sa.keep hL hAcc hBitsWk ia.field.scr (kb.mono rr),by
        rw [show mul 0 P=Point.infinity from by rw [Spec.Weierstrass.mul]; simp]; exact ib.point_tmv (fun _ hx => List.mem_append_left _ hx) jb⟩
  refine WP.mono (nafRun_initCounter_ok b) fun c ⟨cc,kc⟩ => ?_
  refine WP.mono (nafRun_ok hL hJ hAcc hBitsWk hm hC ha hOne hk hP
    (cb.of_keeps kc (by decide)) cc) fun t ⟨kt,ct,_⟩ => ?_
  refine ⟨ia.keep.trans ((Keeps.mono ⟨kb.gpr,kb.rd,kb.wr⟩ (fun _ hr => List.mem_append_left _ hr)).trans
    ((kc.regs.mono (fun _ hr => List.mem_append_right _ hr)).trans kt.keep)),?_,ct⟩
  have ub := nafTable_progUnch kb (fun x hx => List.mem_append_left _ (rr x hx))
  have ut : Unch base (nafTableWrites K wk) c.mem t.mem := kt.mem.mono (by
    intro w hw
    simp only [progW,nafTableWrites,nafWrites,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
    grind)
  rw [kc.2.1] at ut
  exact (ia.unch.trans (ub.trans ut)).mono (by intro w hw; simpa only [List.mem_append,or_self] using hw)

end VG.Proof.Weierstrass.X86
