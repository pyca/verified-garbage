import VerifiedGarbage.Proof.P256.EcdhJac.Frame
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJDigit
import VerifiedGarbage.Proof.P256.EcdhJac.BuildDblu
import VerifiedGarbage.Proof.P256.EcdhJac.Zaddu
import VerifiedGarbage.Proof.Weierstrass.AArch64.CopyKeep

/-! ## `Counter` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

/-- The high counter counts doublings, independently of the low window index. -/
theorem doubleCounter_ok (s : State) {q j : Nat} (hq : 1≤q) (hq5 : q≤5) (hj : j<52)
    (h19 : s.gpr .x19=BitVec.ofNat 64 (2048*q+j)) :
    WP isa (.block [.subImm .x .x19 .x19 2048,.lsr .x .x4 .x19 11]) s fun t =>
      t.gpr .x19=BitVec.ofNat 64 (2048*(q-1)+j) ∧ t.gpr .x4=BitVec.ofNat 64 (q-1) ∧
      Keeps [.x4,.x19] s t := by
  have he : BitVec.ofNat 64 (2048*q+j)-2048=BitVec.ofNat 64 (2048*(q-1)+j) := by
    have hn : 2048*q+j=2048*(q-1)+j+2048 := by omega
    change BitVec.ofNat 64 (2048*q+j)-BitVec.ofNat 64 2048=_
    rw [hn,←BitVec.ofNat_add_ofNat]
    exact BitVec.add_sub_cancel _ _
  have hs : (BitVec.ofNat 64 (2048*(q-1)+j) >>> 11)=BitVec.ofNat 64 (q-1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
    omega
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    show 2048<4096 by decide,show 11<64 by decide,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,
    reduceCtorEq,ite_false,h19,Option.some.injEq,exists_eq_left']
  refine ⟨he,?_,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  · exact (congrArg (fun x : BitVec 64 => x >>> 11) he).trans hs
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

theorem doubleCounter_start (s : State) {j : Nat} (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block [.movz .x .x4 10240 0,.add .x .x19 .x19 .x4]) s fun t =>
      t.gpr .x19=BitVec.ofNat 64 (2048*5+j) ∧ Keeps [.x4,.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    show 16*0<64 by decide,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,
    reduceCtorEq,ite_false,h19,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  · change BitVec.ofNat 64 j+BitVec.ofNat 64 10240=BitVec.ofNat 64 (2048*5+j)
    rw [BitVec.ofNat_add_ofNat,Nat.add_comm]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

theorem countRegLoop_ok (r : Reg) {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop} {n : Nat}
    (hn64 : n < 2 ^ 64)
    (hstep : ∀ j s, 1 ≤ j → j ≤ n → Inv j s →
      WP isa body s fun s' => Inv (j - 1) s' ∧ s'.gpr r = BitVec.ofNat 64 (j - 1))
    (hQ : ∀ s, Inv 0 s → Q s) (hn : 1 ≤ n) {s : State} (hs : Inv n s) :
    WP isa (.loop body (.nonzero .x r)) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ n ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) n s
    ⟨hn, Nat.le_refl _, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' ⟨hi', hz⟩ => ?_
  have hx : (s'.read .x r != 0) = decide (j - 1 ≠ 0) := by
    rw [read_x, hz]
    by_cases hj : j - 1 = 0
    · rw [hj]; rfl
    · rw [decide_eq_true hj, bne_iff_ne, ne_eq]
      intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact hj this
  by_cases hj : j - 1 = 0
  · refine Or.inl ⟨?_, hQ s' (by rw [hj] at hi'; exact hi')⟩
    show some (s'.read .x r != 0) = some false
    rw [hx, hj]; rfl
  · refine Or.inr ⟨?_, j - 1, by omega, by omega, by omega, hi'⟩
    show some (s'.read .x r != 0) = some true
    rw [hx, decide_eq_true hj]

theorem RState.of_keeps {base : Addr} {P Q : Spec.Weierstrass.Point C} {k : Nat} {s t : State}
    {rs : List Reg} (h : RState base P Q k s) (hk : Keeps rs s t) (h0 : Reg.x0∉rs) :
    RState base P Q k t := by
  have hm : t.mem=s.mem := hk.mem
  refine ⟨?_,?_,?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · exact ⟨h.fixed.field.scr.of_keeps hk h0,hm ▸ h.fixed.field.mod,h.fixed.field.sl,
        by simpa only [hm] using h.fixed.field.lt,fun _ _ => rfl⟩
    · simpa only [hm] using h.fixed.zero
    · simpa only [tmv,hm] using h.fixed.peer
    · simpa only [tmv,hm] using h.fixed.one
    · simpa only [hm] using h.fixed.bits
  · intro a ha hb
    apply (h.table a ha hb).congr
    intro i hi
    rw [hm]
  · exact ⟨h.field.scr.of_keeps hk h0,hm ▸ h.field.mod,h.field.sl,
      by simpa only [hm] using h.field.lt,fun _ _ => rfl⟩
  · simpa only [tmv,hm] using h.point

end VG.Proof.P256.EcdhJac

end

/-! ## `BuildStep` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem CoZInv.keeps {base : Addr} {P : Point C} {k m : Nat} {s t : State}
    {rs : List Reg} (hi : CoZInv base P k m s) (hk : Keeps rs s t)
    (hr : rs⊆regs) (hc : t.gpr .x19=BitVec.ofNat 64 m) : CoZInv base P k m t := by
  refine ⟨⟨hi.inv.fixed.keep (frame_build ((AllocatedFrame.of_keeps hk).widenRegs hr)),?_,
    selected_keeps hi.inv.selected hk,hc⟩,?_,?_⟩
  · intro a ha ham; apply (hi.inv.table a ha ham).congr; intro i hi; rw [hk.mem]
  · simpa only [hk.mem] using hi.lt
  · simpa only [tmv,hk.mem] using hi.d

theorem buildIncrement_ok (s : State) {m : Nat} (hc : s.gpr .x19=BitVec.ofNat 64 m) :
    WP isa (.block [.addImm .x .x19 .x19 1]) s fun t =>
      t.gpr .x19=BitVec.ofNat 64 (m+1) ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    show 1<4096 by decide,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,
    hc,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  · exact BitVec.ofNat_add_ofNat _ _
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

theorem buildTest_ok (s : State) :
    WP isa (.block [.subImm .x .x4 .x19 16]) s fun t =>
      t.gpr .x4=s.gpr .x19-16 ∧ Keeps [.x4] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    show 16<4096 by decide,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,
    Option.some.injEq,exists_eq_left']
  refine ⟨rfl,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write,hr,ite_false]

theorem buildStep_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k m : Nat} {s : State} (hP : onCurve C P=true)
    (hm2 : 2≤m) (hm15 : m≤15) (hi : CoZInv base P k m s) :
    WP isa Impl.P256.EcdhJac.buildStep s fun t =>
      Frame base buildWork s t ∧ CoZInv base P k (m+1) t ∧
      t.gpr .x4=BitVec.ofNat 64 (m+1)-16 := by
  unfold Impl.P256.EcdhJac.buildStep
  refine WP.seq (WP.mono (buildIncrement_ok s hi.inv.counter) fun a ⟨ca,ka⟩ => ?_)
  have fa := hi.inv.fixed.keep (frame_build ((AllocatedFrame.of_keeps ka).widenRegs (by decide)))
  have pa := selected_keeps hi.inv.selected ka
  have la : ∀x∈[K.D.x,K.D.y],wordsVal a.mem base x 4<C.p := by simpa only [ka.mem] using hi.lt
  have da : InvJ C (tmv C 4 base a K.D.x) (tmv C 4 base a K.D.y) (tmv C 4 base a K.E.z) P := by
    simpa only [tmv,ka.mem] using hi.d
  refine WP.seq (WP.mono (EcdhTable.zaddu_ok hC ha hO hP hm2 hm15 fa pa la da) fun b ⟨kb,fb,pb,lb,db,cb⟩ => ?_)
  have ta : TblOk base P m a := by
    intro j hj hjm; apply (hi.inv.table j hj hjm).congr; intro i hi; rw [ka.mem]
  have tb := table_keep ta (by omega) kb
  rw [WP.block_append_iff]
  refine WP.mono (storeCoZ_ok (m:=m+1) (by omega) (by omega) fb (by simpa using tb) pb lb db (cb.trans ca)) fun d ⟨kd,id⟩ => ?_
  refine WP.mono (buildTest_ok d) fun t ⟨ct,kt⟩ => ?_
  refine ⟨(frame_build ((AllocatedFrame.of_keeps ka).widenRegs (by decide))).trans
    ((frame_build kb).trans (kd.trans ((AllocatedFrame.of_keeps kt).widenRegs (by decide)))),
    id.keeps kt (by decide) ?_,ct.trans ?_⟩
  · rw [kt.gpr .x19 (by decide),id.inv.counter]
  · rw [id.inv.counter]
end VG.Proof.P256.EcdhJac

end

/-! ## `Build` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

theorem buildLoop_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k : Nat} {s : State} (hP : onCurve C P=true)
    (hi : CoZInv base P k 2 s) :
    WP isa (.loop Impl.P256.EcdhJac.buildStep (.nonzero .x .x4)) s fun t =>
      Frame base buildWork s t ∧ CoZInv base P k 16 t := by
  refine WP.loop (M:=isa)
    (fun j t => 1≤j ∧ j≤14 ∧ Frame base buildWork s t ∧ CoZInv base P k (16-j) t)
    (fun j a ⟨hj,hj14,hf,hi⟩ => ?_) 14 s ⟨by decide,by decide,AllocatedFrame.refl _ _ _ _,hi⟩
  refine WP.mono (buildStep_ok hC ha hO hP (by omega) (by omega) hi) fun t ⟨kt,it,ct⟩ => ?_
  have hn : 16-j+1=16-(j-1) := by omega
  rw [hn] at it ct
  have hz : (t.read .x .x4 != 0)=decide (j-1≠0) := by
    rw [read_x,ct]
    by_cases h : j-1=0
    · rw [h]; rfl
    · rw [decide_eq_true h,bne_iff_ne,ne_eq]
      intro he
      have hh : BitVec.ofNat 64 (16-(j-1)) = (16 : BitVec 64) := by bv_omega
      have he' := congrArg BitVec.toNat hh
      simp only [BitVec.toNat_ofNat,show (16 : BitVec 64).toNat=16 from rfl,
        Nat.mod_eq_of_lt (show 16-(j-1)<2^64 by omega)] at he'
      omega
  by_cases h : j-1=0
  · refine Or.inl ⟨?_,hf.trans kt,?_⟩
    · show some (t.read .x .x4 != 0)=some false
      rw [hz,h]; rfl
    · simpa only [h,Nat.sub_zero] using it
  · refine Or.inr ⟨?_,j-1,by omega,by omega,by omega,hf.trans kt,it⟩
    show some (t.read .x .x4 != 0)=some true
    rw [hz,decide_eq_true h]

/-- The fixed sixteen-entry co-Z table supports every scalar, including invalid inputs. -/
theorem build_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k : Nat} {s : State} (hP : onCurve C P=true)
    (hf : Fixed base P k s) :
    WP isa Impl.P256.EcdhJac.build s fun t =>
      Frame base buildWork s t ∧ Fixed base P k t ∧ TblOk base P 16 t := by
  unfold Impl.P256.EcdhJac.build
  refine WP.seq (WP.mono (buildStart_ok hf) fun a ⟨ka,ia⟩ => ?_)
  obtain ⟨tr,b,he,kb,ib⟩ := buildDblu_ok hC ha hO hP ia
  cases he with
  | seq h1 h2 =>
    obtain ⟨tr,t,ht,kt,it⟩ := buildLoop_ok hC ha hO hP ib
    exact ⟨_,t,.seq h1 (.seq h2 ht),ka.trans (kb.trans kt),it.inv.fixed,it.inv.table⟩
end VG.Proof.P256.EcdhJac

end

/-! ## `Masks` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)
open Spec.Weierstrass

def digitMagnitude (k j : Nat) := magH 16 (Window5.nib (k+offset) j)
def maskCode : List Instr := nzMask 4 K.R.z++selPt 4 K.D K.E K.D++tc.digit++
  [zero7,.movz .x .x5 1 0,.subs .x .x16 .x2 .x5,.sbc .x .x3 .x7 .x7]++selPt 4 K.R K.D K.R

private theorem infinityMask_ok {base : Addr} {s : State} (hs : Scr s base 8192) :
    WP isa (.block (nzMask 4 K.R.z++selPt 4 K.D K.E K.D)) s fun b =>
      AllocatedFrame allocatedRegs base work s b ∧
      (∀ i<3,wordsVal b.mem base (512+32*i) 4=wordsVal s.mem base (512+32*i) 4) ∧
      (∀ i<3,wordsVal b.mem base (608+32*i) 4=
        if wordsVal s.mem base 576 4=0 then wordsVal s.mem base (704+32*i) 4
        else wordsVal s.mem base (608+32*i) 4) := by
  rw [WP.block_append_iff]
  refine WP.mono (nzMask_ok hs (by decide) (by decide : 576+8*4≤8192) (by decide))
    fun a ⟨a3,ka⟩ => ?_
  change a.gpr .x3=mask (wordsVal s.mem base 576 4≠0) at a3
  refine WP.mono (selPtKeep_ok (hs.of_keeps ka (by decide))
    (decide (wordsVal s.mem base 576 4≠0)) (by simpa only [mask,decide_eq_true_eq] using a3)
    (n:=4) (o:=K.D) (a:=K.E) (by decide) (by decide) (by decide)) fun b ⟨bx,by',bz,kb,ub⟩ => ?_
  have ud : Unch base [(608,32),(640,32),(672,32)] a.mem b.mem := fun x hx =>
    ub x (hx (608,32) (by decide)) (hx (640,32) (by decide)) (hx (672,32) (by decide))
  have fb : AllocatedFrame allocatedRegs base work s b := ⟨
    (Keeps.regs ka).mono (by decide) |>.trans (kb.mono (by decide)),by
      simpa only [ka.mem] using ud.cover (by decide : ∀ w∈[(608,32),(640,32),(672,32)],
        ∃ r∈work,r.1≤w.1 ∧ w.1+w.2≤r.1+r.2)⟩
  have sameR : ∀ i<3,wordsVal b.mem base (512+32*i) 4=wordsVal s.mem base (512+32*i) 4 := by
    intro i hi
    rw [ud.wordsVal (by
      have hh : ∀ i<3,∀ w∈[(608,32),(640,32),(672,32)],512+32*i+32≤w.1 ∨ w.1+w.2≤512+32*i := by decide
      exact hh i hi) (by omega),ka.mem]
  have sameD : ∀ i<3,wordsVal b.mem base (608+32*i) 4=
      if wordsVal s.mem base 576 4=0 then wordsVal s.mem base (704+32*i) 4
      else wordsVal s.mem base (608+32*i) 4 := by
    simp only [ka.mem,decide_eq_true_eq] at bx by' bz
    intro i hi
    rcases (by omega : i=0 ∨ i=1 ∨ i=2) with rfl|rfl|rfl
    all_goals simp only [Nat.mul_zero,Nat.add_zero,Nat.reduceMul,Nat.reduceAdd]
    · change wordsVal b.mem base 608 4=(if _ then wordsVal s.mem base 608 4 else wordsVal s.mem base 704 4) at bx
      simpa only [ne_eq,ite_not] using bx
    · change wordsVal b.mem base 640 4=(if _ then wordsVal s.mem base 640 4 else wordsVal s.mem base 736 4) at by'
      simpa only [ne_eq,ite_not] using by'
    · change wordsVal b.mem base 672 4=(if _ then wordsVal s.mem base 672 4 else wordsVal s.mem base 768 4) at bz
      simpa only [ne_eq,ite_not] using bz
  exact ⟨fb,sameR,sameD⟩

def digitMaskCode : List Instr := tc.digit++
  [zero7,.movz .x .x5 1 0,.subs .x .x16 .x2 .x5,.sbc .x .x3 .x7 .x7]++selPt 4 K.R K.D K.R

private theorem magnitude_zero (a : Nat) (ha : a≤16) :
    BitVec.ofNat 64 a=0 ↔ a=0 := by
  constructor
  · intro h
    have hh := congrArg BitVec.toNat h
    change a%2^64=0 at hh
    omega
  · intro h; rw [h]; rfl

private theorem zeroSelect_ok {base : Addr} {c : State} {a : Nat}
    (hs : Scr c base 8192) (ha : a≤16) (h2 : c.gpr .x2=BitVec.ofNat 64 a) :
    WP isa (.block (([zero7,.movz .x .x5 1 0,.subs .x .x16 .x2 .x5,.sbc .x .x3 .x7 .x7] : List Instr)++selPt 4 K.R K.D K.R)) c
      fun t => AllocatedFrame allocatedRegs base work c t ∧
        ∀ i<3,wordsVal t.mem base (512+32*i) 4=
          if a=0 then wordsVal c.mem base (512+32*i) 4 else wordsVal c.mem base (608+32*i) 4 := by
  rw [WP.block_append_iff]
  have ce : c.gpr .x2=0 ↔ a=0 := h2 ▸ magnitude_zero a ha
  refine WP.mono (booth_eqMask_ok c) fun d ⟨d3,kd⟩ => ?_
  refine WP.mono (selPtKeep_ok (hs.of_keeps kd (by decide))
    (decide (a=0)) (by simpa only [mask,decide_eq_true_eq,ce] using d3)
    (n:=4) (o:=K.R) (a:=K.D) (by decide) (by decide) (by decide)) fun t ⟨tx,ty,tz,kt,ut⟩ => ?_
  have ur : Unch base [(512,32),(544,32),(576,32)] d.mem t.mem := fun x hx =>
    ut x (hx (512,32) (by decide)) (hx (544,32) (by decide)) (hx (576,32) (by decide))
  have fd : AllocatedFrame allocatedRegs base work c d := (AllocatedFrame.of_keeps kd).widenRegs (by decide)
  have ft : AllocatedFrame allocatedRegs base work d t := ⟨kt.mono (by decide),ur.cover (by decide)⟩
  refine ⟨fd.trans ft,?_⟩
  simp only [kd.mem,decide_eq_true_eq] at tx ty tz
  intro i hi
  have e : wordsVal t.mem base (512+32*i) 4=
      if a=0 then wordsVal c.mem base (512+32*i) 4 else wordsVal c.mem base (608+32*i) 4 := by
    rcases (by omega : i=0 ∨ i=1 ∨ i=2) with rfl|rfl|rfl
    · exact tx
    · exact ty
    · exact tz
  exact e


private theorem digitMask_ok {base : Addr} {P : Point C} {k j : Nat} {b : State}
    (fxb : Fixed base P k b) (hj : j<52) (h19 : b.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block digitMaskCode) b fun t => AllocatedFrame allocatedRegs base work b t ∧
      ∀ i<3,wordsVal t.mem base (512+32*i) 4=
        if digitMagnitude k j=0 then wordsVal b.mem base (512+32*i) 4
        else wordsVal b.mem base (608+32*i) 4 := by
  rw [digitMaskCode,List.append_assoc,WP.block_append_iff]
  refine WP.mono (digitW_ok tc fxb.field.scr (k:=k+offset) (j:=j) (N:=260)
    (by decide) (by decide) (by change 5*j+5≤260; omega) (by decide) (by decide) h19 fxb.bits)
    fun c ⟨c2,kc⟩ => ?_
  have c2' : c.gpr .x2=BitVec.ofNat 64 (digitMagnitude k j) := by
    change c.gpr .x2=BitVec.ofNat 64 (magH 16 (combWin 5 (k+offset) j)) at c2
    simpa only [Window5.combWin_five,digitMagnitude] using c2
  refine WP.mono (zeroSelect_ok (fxb.field.scr.of_keeps kc (by decide))
    (magH_le (Window5.nib_lt (k+offset) j)) c2') fun t ⟨ft,hv⟩ => ?_
  refine ⟨((AllocatedFrame.of_keeps kc).widenRegs (by decide)).trans ft,?_⟩
  intro i hi
  have hh := hv i hi
  rw [kc.mem] at hh
  exact hh

theorem masks_ok {base : Addr} {P : Point C} {k j : Nat} {s : State}
    (hf : Fixed base P k s) (hj : j<52) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block maskCode) s fun t => AllocatedFrame allocatedRegs base work s t ∧
      ∀ i<3,wordsVal t.mem base (512+32*i) 4=
        if digitMagnitude k j=0 then wordsVal s.mem base (512+32*i) 4
        else if wordsVal s.mem base 576 4=0 then wordsVal s.mem base (704+32*i) 4
        else wordsVal s.mem base (608+32*i) 4 := by
  rw [show maskCode=(nzMask 4 K.R.z++selPt 4 K.D K.E K.D)++digitMaskCode by
    simp only [maskCode,digitMaskCode,List.append_assoc],WP.block_append_iff]
  refine WP.mono (infinityMask_ok hf.field.scr) fun b ⟨fb,sameR,sameD⟩ => ?_
  refine WP.mono (digitMask_ok (hf.keep (frame_build (fb.widenRegs allocated_regs))) hj
    ((fb.regs.gpr _ allocatedRegs_x19).trans h19)) fun t ⟨ft,hv⟩ => ?_
  refine ⟨fb.trans ft,?_⟩
  intro i hi
  rw [hv i hi,sameR i hi,sameD i hi]

end VG.Proof.P256.EcdhJac

end
