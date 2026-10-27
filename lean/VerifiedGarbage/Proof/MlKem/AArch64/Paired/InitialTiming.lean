module
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Initial
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Impl.MlKem.AArch64

structure OneReadyW (w16 : Bool) (B : Nat→Byte) (buf out slot : Nat) (s : State) : Prop where
  env : Rej8.EnvW w16 168 B (s.gpr .x19+BitVec.ofNat 64 buf) (s.gpr .x28+BitVec.ofNat 64 out) s
  constants : Rej8.Constants s
  out0 : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 slot) 8
  out1 : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 (slot+8)) 8
  apart : (polyRegion (s.gpr .x28+BitVec.ofNat 64 out)).Disjoint ⟨s.gpr .x19+BitVec.ofNat 64 slot,16⟩

structure InitialReadyW (w16 : Bool) (A B : Nat→Byte) (a b : Nat) (s : State) : Prop where
 left : OneReadyW w16 A 400 a 1680 s
 right : OneReadyW w16 B 904 b 1696 s
 far : (polyRegion (s.gpr .x28+BitVec.ofNat 64 a)).Disjoint ⟨s.gpr .x19,2048⟩
 table : ∀mask<256,(Region.mk (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16).Disjoint ⟨s.gpr .x19,2048⟩

theorem initialStart_ct (a b : Nat) : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block (ptrTo .x21 .x28 a ++ ptrTo .x23 .x28 b ++
      ([.addImm .x .x20 .x19 400,.addImm .x .x1 .x19 1680,.movz .x .x22 1 0] : List Instr))) := by
  unfold ptrTo
  split <;> split <;> exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

theorem oneEntry_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block oneEntry) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

theorem oneNext_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block oneNext) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

theorem initialEnd_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block [mov .x6 .x22]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

theorem oneTail_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs [.x1]))
    (.block (oneStore ++ oneNext)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x1]) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

/-- An iteration of `rejectBoth` from a stream ready at the same place in both runs. -/
theorem oneBody_relCT {w16 : Bool} {t v : State} {B : Nat→Byte}
    (pt : OneReadyR w16 B t) (pv : OneReadyR w16 B v) (sp : t.sp=v.sp) (h20 : t.gpr .x20=v.gpr .x20)
    (h21 : t.gpr .x21=v.gpr .x21) (h1 : t.gpr .x1=v.gpr .x1) (h16 : t.gpr .x16=v.gpr .x16) :
    RelCT isa (fun x y=>x=t ∧ y=v) (oneBody w16) (fun _ _=>True) := by
  change RelCT isa _ (.seq (.block oneEntry) (.seq (Rej8.rejLoop w16) (.block (oneStore ++ oneNext)))) _
  refine RelCT.seq (R:=fun x y : State=>Rej8.EntryW w16 [] 168 B (t.gpr .x20) (t.gpr .x21) x ∧
    Rej8.EntryW w16 [] 168 B (t.gpr .x20) (t.gpr .x21) y ∧ x.sp=y.sp ∧ x.gpr .x16=y.gpr .x16 ∧
    x.gpr .x1=y.gpr .x1) ?_ ?_
  · intro x y tx ty x' y' h ex ey
    rcases h with ⟨rfl,rfl⟩
    obtain ⟨kx,px⟩ := exec_post (oneEntry_ok pt) ex
    obtain ⟨ky,py⟩ := exec_post (oneEntry_ok pv) ey
    refine ⟨oneEntry_ct x y tx ty x' y' trivial trivial (agree_of sp (by simp)) ex ey,px,
      by rw [h20,h21]; exact py,kx.sp.trans (sp.trans ky.sp.symm),
      by rw [kx.get .x16,ky.get .x16,h16],by rw [kx.get .x1,ky.get .x1,h1]⟩
  refine RelCT.seq (R:=fun x y : State=>x.sp=y.sp ∧ x.gpr .x1=y.gpr .x1) ?_ ?_
  · intro x y tx ty x' y' h ex ey
    obtain ⟨ht,hx,hy⟩ := Rej8.segment_relCT h.1 h.2.1 h.2.2.1 h.2.2.2.1 (by decide) (by decide)
      x y tx ty x' y' ⟨rfl,rfl⟩ ex ey
    exact ⟨ht,hx.keep.sp.trans (h.2.2.1.trans hy.keep.sp.symm),
      by rw [hx.keep.get .x1,hy.keep.get .x1,h.2.2.2.2]⟩
  · intro x y tx ty x' y' h ex ey
    exact ⟨oneTail_ct x y tx ty x' y' trivial trivial
      (agree_of h.1 (by intro r hr; rw [List.mem_singleton.mp hr]; exact h.2)) ex ey,trivial⟩

/-- Between the iterations of `rejectBoth` (for the trace): the second stream ready. -/
def InitialMid (w16 : Bool) (B : Nat→Byte) (p oB : Addr) (s t : State) : Prop :=
  Keep initialRegs s t ∧ Rej8.Constants t ∧ t.gpr .x20=p+BitVec.ofNat 64 904 ∧ t.gpr .x21=oB ∧
    t.gpr .x1=p+BitVec.ofNat 64 1696 ∧ Rej8.EnvW w16 168 B (p+BitVec.ofNat 64 904) oB t

theorem initialMid_of {w16 : Bool} {s t u : State} {A B : Nat→Byte} {a b : Nat}
    (h : InitialReadyW w16 A B a b s)
    (ht : InitialInv w16 A B (s.gpr .x19) (s.gpr .x28+BitVec.ofNat 64 a) (s.gpr .x28+BitVec.ofNat 64 b) s 0 t)
    (hu : OnePostW w16 A t u) :
    InitialMid w16 B (s.gpr .x19) (s.gpr .x28+BitVec.ofNat 64 b) s u := by
  obtain ⟨kt,_,ct,t20,t21,t23,t1,_,ea,eb⟩ := ht
  have sA : Region.Sub ⟨s.gpr .x19+BitVec.ofNat 64 1680,16⟩ ⟨s.gpr .x19,2048⟩ := Offset.sub_base _ (by decide)
  have hf : Frame [polyRegion (s.gpr .x28+BitVec.ofNat 64 a),⟨s.gpr .x19+BitVec.ofNat 64 1680,16⟩] t.mem u.mem := by
    have := hu.frame; rw [t1,t21] at this; exact this
  refine ⟨(kt.trans hu.keep).mono,hu.constants,by rw [hu.x20,t20,ptr_add],by rw [hu.x21,t23],
    by rw [hu.x1,t1,ptr_add],?_⟩
  refine eb.frame hu.keep.rd hu.keep.wr (hu.keep.get .x16) hf ?_ ?_
  · simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    exact ⟨(h.far.sub_right (Offset.sub_base _ (by decide))).symm,
      Offset.disjoint (s.gpr .x19) (d:=904) (n:=508) (e:=1680) (k:=16) (by decide) (by decide) (by decide)⟩
  · intro mask hm
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    exact ⟨ea.tableDisj mask hm,by rw [kt.get .x16]; exact (h.table mask hm).sub_right sA⟩

theorem initial_relCT {w16 : Bool} {s u : State} {A B : Nat→Byte} {a b : Nat}
 (ha : a<65536) (hb : b<65536) (hs : InitialReadyW w16 A B a b s) (hu : InitialReadyW w16 A B a b u)
 (sp : s.sp=u.sp) (h19 : s.gpr .x19=u.gpr .x19) (h28 : s.gpr .x28=u.gpr .x28)
 (h16 : s.gpr .x16=u.gpr .x16) :
 RelCT isa (fun x y=>x=s ∧ y=u) (initialCode a b w16) (fun _ _=>True) := by
  let J := fun (r : State) => InitialInv w16 A B (r.gpr .x19) (r.gpr .x28+BitVec.ofNat 64 a)
    (r.gpr .x28+BitVec.ofNat 64 b) r 0
  let M := fun (r : State) => InitialMid w16 B (r.gpr .x19) (r.gpr .x28+BitVec.ofNat 64 b) r
  let I : Nat → State → State → Prop := fun n t v =>
    (n=2 ∧ J s t ∧ J u v) ∨ (n=1 ∧ M s t ∧ M u v)
  have ready0 {r t : State} (hr : InitialReadyW w16 A B a b r) (ht : J r t) : OneReadyR w16 A t := by
    obtain ⟨kt,_,ct,t20,t21,_,t1,_,ea,_⟩ := ht
    refine ⟨by rw [t20,t21]; exact ea,ct,?_,?_,?_⟩
    · rw [t1,kt.wr]; exact hr.left.out0
    · rw [t1,kt.wr,BitVec.add_assoc]; exact hr.left.out1
    · rw [t1,t21]; exact hr.left.apart
  have ready1 {r t : State} (hr : InitialReadyW w16 A B a b r) (ht : M r t) : OneReadyR w16 B t := by
    obtain ⟨kt,ct,t20,t21,t1,eb⟩ := ht
    refine ⟨by rw [t20,t21]; exact eb,ct,?_,?_,?_⟩
    · rw [t1,kt.wr]; exact hr.right.out0
    · rw [t1,kt.wr,BitVec.add_assoc]; exact hr.right.out1
    · rw [t1,t21]; exact hr.right.apart
  have start : RelCT isa (fun x y=>x=s ∧ y=u)
      (.block (ptrTo .x21 .x28 a ++ ptrTo .x23 .x28 b ++
        ([.addImm .x .x20 .x19 400,.addImm .x .x1 .x19 1680,.movz .x .x22 1 0] : List Instr))) (I 2) := by
    intro x y tx ty x' y' h ex ey
    rcases h with ⟨rfl,rfl⟩
    exact ⟨initialStart_ct a b x y tx ty x' y' trivial trivial (agree_of sp (by simp)) ex ey,
      .inl ⟨rfl,exec_post (initialStart_ok ha hb hs.left.env hs.right.env hs.left.constants) ex,
        exec_post (initialStart_ok ha hb hu.left.env hu.right.env hu.left.constants) ey⟩⟩
  have loop : RelCT isa (I 2) (.loop (oneBody w16) (.nonzero .x .x6)) (fun t v=>t.sp=v.sp) := by
    refine RelCT.loop (M:=isa) I (fun n => ?_) 2
    intro t v tt tv t' v' hI et ev
    rcases hI with ⟨rfl,it,iv⟩|⟨rfl,it,iv⟩
    · have tq := oneBody_relCT (ready0 hs it) (ready0 hu iv) (it.1.sp.trans (sp.trans iv.1.sp.symm))
        (by rw [it.2.2.2.1,iv.2.2.2.1,h19]) (by rw [it.2.2.2.2.1,iv.2.2.2.2.1,h28])
        (by rw [it.2.2.2.2.2.2.1,iv.2.2.2.2.2.2.1,h19]) (by rw [it.1.get .x16,iv.1.get .x16,h16])
        t v tt tv t' v' ⟨rfl,rfl⟩ et ev
      have pt := exec_post (oneBody_ok (ready0 hs it)) et
      have pv := exec_post (oneBody_ok (ready0 hu iv)) ev
      have e6 : ∀ {r w w' : State}, J r w → OnePostW w16 A w w' →
          isa.eval (.nonzero .x .x6) w'=some true := by
        intro r w w' hw hw'
        rw [eval_nonzero,hw'.x6,hw.2.2.2.2.2.2.1,hw.1.get .x19,x6_after]; rfl
      refine ⟨tq.1,by rw [e6 it pt,e6 iv pv],fun h => (by rw [e6 it pt] at h; cases h),
        fun _ => ⟨1,by decide,.inr ⟨rfl,initialMid_of hs it pt,initialMid_of hu iv pv⟩⟩⟩
    · have tq := oneBody_relCT (ready1 hs it) (ready1 hu iv) (it.1.sp.trans (sp.trans iv.1.sp.symm))
        (by rw [it.2.2.1,iv.2.2.1,h19]) (by rw [it.2.2.2.1,iv.2.2.2.1,h28])
        (by rw [it.2.2.2.2.1,iv.2.2.2.2.1,h19]) (by rw [it.1.get .x16,iv.1.get .x16,h16])
        t v tt tv t' v' ⟨rfl,rfl⟩ et ev
      have pt := exec_post (oneBody_ok (ready1 hs it)) et
      have pv := exec_post (oneBody_ok (ready1 hu iv)) ev
      have e6 : ∀ {r w w' : State}, M r w → OnePostW w16 B w w' →
          isa.eval (.nonzero .x .x6) w'=some false := by
        intro r w w' hw hw'
        rw [eval_nonzero,hw'.x6,hw.2.2.2.2.1,hw.1.get .x19,x6_after]; rfl
      refine ⟨tq.1,by rw [e6 it pt,e6 iv pv],
        fun _ => pt.keep.sp.trans (it.1.sp.trans (sp.trans (iv.1.sp.symm.trans pv.keep.sp.symm))),
        fun h => (by rw [e6 it pt] at h; cases h)⟩
  refine RelCT.seq start (RelCT.seq loop ?_)
  intro t v tt tv t' v' h et ev
  exact ⟨initialEnd_ct t v tt tv t' v' trivial trivial (agree_of h (by simp)) et ev,trivial⟩

end VG.Proof.MlKem.AArch64.Paired
