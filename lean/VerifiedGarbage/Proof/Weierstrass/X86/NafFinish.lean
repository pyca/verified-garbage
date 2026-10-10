import VerifiedGarbage.Proof.Weierstrass.X86.NafSum
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect

/-! ## `NafDigit` -/

section

/-! A zero digit is skipped; a nonzero digit contributes its signed odd multiple. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafMagnitude_byte (k j : Nat) : nafMagnitude (Naf5.byte k j)=Naf5.magnitude k j :=
  Naf5.byte_magnitude k j

theorem nafNegative_byte (k j : Nat) : nafNegative (Naf5.byte k j)=Naf5.negative k j :=
  Naf5.byte_negative k j

theorem nafDigit_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk k j : Nat}
    (hL : NafLay K size) (hJ : K.J=65) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hj : j<257) {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : NafCore K C base size P (Naf5.byte k) (2*Naf5.residual k (j+1)) s)
    (hc : s.gpr .esi=BitVec.ofNat 32 j) :
    WP isa (Naf.digit K F) s fun t => ProgKeep K.M base wk (winOther K) s t ∧
      NafCore K C base size P (Naf5.byte k) (Naf5.residual k j) t := by
  rw [Naf.digit]
  apply WP.seq
  refine WP.mono (nafRead_ok h.field.scr (by have:=hL.bits; omega) hc (h.stable.bits j hj))
    fun u ⟨u8,uz,ku⟩ => ?_
  have cu := h.of_keeps ku (by decide)
  have kp : ProgKeep K.M base wk (winOther K) s u := nafPrefix_keep ku (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> simp [clob])
  refine WP.ite (decide (Naf5.byte k j=0)) uz (fun hz => ?_) (fun hn => ?_)
  · have hm0 := (Naf5.byte_zero_iff k j).mp (of_decide_eq_true hz)
    have he : Naf5.residual k j=2*Naf5.residual k (j+1) := by
      have hh := Naf5.recurrence k j
      rw [hm0] at hh
      split at hh <;> omega
    apply WP.block_nil
    exact ⟨kp,he.symm ▸ cu⟩
  · have hm0 : Naf5.magnitude k j≠0 := fun he =>
      of_decide_eq_false hn ((Naf5.byte_zero_iff k j).mpr he)
    apply WP.seq
    refine WP.mono (nafEntry_ok hL hAcc hBitsWk hm
      (by rw [nafMagnitude_byte]; omega)
      (by rw [nafMagnitude_byte]; exact Naf5.magnitude_le k j)
      (by rw [nafMagnitude_byte]; exact (Naf5.magnitude_odd_or_zero k j).resolve_left hm0)
      cu u8) fun v ⟨kv,cv,iv,jv⟩ => ?_
    simp only [nafNegative_byte,nafMagnitude_byte] at jv
    exact WP.mono (nafAdd_ok hL hJ hAcc hBitsWk hm hC ha hOne hP
      (Naf5.onCurve_point hC hP k j) (Naf5.add_step hC hP k j) cv iv jv)
      fun t ⟨kt,ct⟩ => ⟨kp.trans (kv.trans kt),ct⟩

end VG.Proof.Weierstrass.X86

end

/-! ## `NafStep` -/

section

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

end

/-! ## `NafLoop` -/

section

/-! The 256 counted Jacobian iterations and the extra carry digit at bit 256. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafLoop_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk k : Nat}
    (hL : NafLay K size) (hJ : K.J=65) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : NafCore K C base size P (Naf5.byte k) (Naf5.residual k 256) s)
    (hc : s.gpr .esi=256) :
    WP isa (.loop (Naf.windowStep K F) .ne) s fun t =>
      NafLoopKeep K base wk s t ∧ NafCore K C base size P (Naf5.byte k) k t ∧ t.gpr .esi=0 := by
  let I := fun j t => NafLoopKeep K base wk s t ∧
    NafCore K C base size P (Naf5.byte k) (Naf5.residual k j) t ∧ t.gpr .esi=BitVec.ofNat 32 j
  apply countLoop_ok (Inv:=I) (n:=256)
  · intro j a hj1 hj256 hi
    obtain ⟨ka,ca,ac⟩ := hi
    have he : j-1+1=j := by omega
    have cp : NafCore K C base size P (Naf5.byte k) (Naf5.residual k (j-1+1)) a := he.symm ▸ ca
    have ap : a.gpr .esi=BitVec.ofNat 32 (j-1+1) := he.symm ▸ ac
    refine WP.mono (nafStep_ok hL hJ hAcc hBitsWk hm hC ha hOne (by omega) hP cp ap)
      fun t ⟨kt,ct,tc,tz⟩ => ⟨⟨ka.trans kt,ct,tc⟩,tz⟩
  · intro t ht
    obtain ⟨kt,ct,tc⟩ := ht
    exact ⟨kt,ct,tc⟩
  · decide
  · exact ⟨NafLoopKeep.refl K base wk s,h,hc⟩

theorem nafRun_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk k : Nat}
    (hL : NafLay K size) (hJ : K.J=65) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hk : k<2^256) {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : NafCore K C base size P (Naf5.byte k) 0 s) (hc : s.gpr .esi=256) :
    WP isa (.seq (Naf.digit K F) (.loop (Naf.windowStep K F) .ne)) s fun t =>
      NafLoopKeep K base wk s t ∧ NafCore K C base size P (Naf5.byte k) k t ∧ t.gpr .esi=0 := by
  have he : 2*Naf5.residual k (256+1)=0 := by rw [Naf5.residual_zero257 hk,Nat.mul_zero]
  apply WP.seq
  refine WP.mono (nafDigit_ok hL hJ hAcc hBitsWk hm hC ha hOne (by decide) hP (he.symm ▸ h) hc)
    fun a ⟨ka,ca⟩ => ?_
  have ac : a.gpr .esi=256 := (ka.gpr _ (by decide)).trans hc
  refine WP.mono (nafLoop_ok hL hJ hAcc hBitsWk hm hC ha hOne hP ca ac)
    fun t ⟨kt,ct,tc⟩ => ⟨?_,ct,tc⟩
  have kp : NafLoopKeep K base wk s a :=
    ⟨Keeps.mono ⟨ka.gpr,ka.rd,ka.wr⟩ (fun _ hr => List.mem_append_left _ hr),ka.unch⟩
  exact kp.trans kt

end VG.Proof.Weierstrass.X86

end

/-! ## `NafWindowInit` -/

section

/-! Public multiplication from an affine input and its recoded scalar bytes. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

structure NafInput (K : WinCfg) (C : Curve) (base : Addr) (P : Point C) (k : Nat) (s : State) : Prop where
  point : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y) (tmv C K.M.n base s K.P.z) P
  zero : wordsVal s.mem base K.zero K.M.n=0
  bits : ∀ i<257,s.mem (off base (K.bits+i))=Naf5.byte k i

theorem nafRun_initCounter_ok (s : State) :
    WP isa (.block [.mov .esi (.imm 256)]) s fun t => t.gpr .esi=256 ∧ CKeeps [.esi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,
    Option.map_some,RegUpd.gpr_setReg,ite_true,Option.some.injEq,exists_eq_left']
  exact ⟨trivial,fun r hr => by simp only [List.mem_singleton] at hr; simp only [RegUpd.gpr_setReg,hr,ite_false],rfl,rfl,rfl⟩

theorem nafWindow_init_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk k : Nat}
    (hL : NafLay K size) (hJ : K.J=65) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (hI : Inv K.M base size C.p (·∈nafSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hp : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P)
    (hz : wordsVal s.mem base K.zero K.M.n=0)
    (hb : ∀ i<257,s.mem (off base (K.bits+i))=Naf5.byte k i) :
    WP isa (.seq (Naf.table K F)
      (.block (Jacobian.infinity K K.R ++ ([.mov .esi (.imm 256)] : List Instr)))) s fun t =>
      KeepRegs (nafTableClob K) s t ∧ Unch base (nafTableWrites K wk) s.mem t.mem ∧
      NafCore K C base size P (Naf5.byte k) 0 t ∧ t.gpr .esi=256 := by
  have rr : ∀ x∈rcbW K.S K.R,x∈winOther K := by
    intro x hx; simp only [rcbW,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have rs : ∀ x∈jacCoords K.R,x∈nafSlots K := fun x hx =>
    nafOther_slots K x (rr x (by simp only [jacCoords,rcbW,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind))
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
  rw [WP.block_append_iff]
  refine WP.mono (infinityPoint_ok hL.lay hAcc rs ia.field hOne) fun b ⟨eb,kb,ib,jb⟩ => ?_
  have cb : NafCore K C base size P (Naf5.byte k) 0 b :=
    ⟨(ib.sub (fun _ hx => List.mem_append_right _ hx)).to_tmv,
      sa.keep hL hAcc hBitsWk ia.field.scr (kb.mono rr),by
        rw [show mul 0 P=Point.infinity from by rw [Spec.Weierstrass.mul]; simp]; exact ib.point_tmv (fun _ hx => List.mem_append_left _ hx) jb⟩
  refine WP.mono (nafRun_initCounter_ok b) fun c ⟨cc,kc⟩ => ?_
  refine ⟨ia.keep.trans ((Keeps.mono ⟨kb.gpr,kb.rd,kb.wr⟩ (fun _ hr => List.mem_append_left _ hr)).trans
    (kc.regs.mono (fun _ hr => List.mem_append_right _ hr))),?_,cb.of_keeps kc (by decide),cc⟩
  have ub := nafTable_progUnch kb (fun x hx => List.mem_append_left _ (rr x hx))
  rw [kc.2.1]
  exact (ia.unch.trans ub).mono (by intro w hw; simpa only [List.mem_append,or_self] using hw)

end VG.Proof.Weierstrass.X86

end

/-! ## `NafWindow` -/

section

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

end

/-! ## `NafFinish` -/

section

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

end
