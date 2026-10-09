import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourScalarPair
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourTaint

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64 (Keep eval_zero eq_zero_iff)
open VG.Impl.MlDsa.AArch64.Sample (rbTry)

structure ScalarPairReady (η : Nat) (p : Addr) (L : List Zq) (b : Byte) (s : State) : Prop where
 consts : ScalarConsts η s
 bound : L.length≤256
 stored : Stored s.mem p L
 output : s.gpr .x3=coeffAddr p L.length
 remaining : (s.gpr .x4).toNat=256-L.length
 byte : s.gpr .x6=b.setWidth 64
 low : s.gpr .x7=BitVec.ofNat 64 (b.toNat%16)
 write : ∀j<256,InRegions s.wr (coeffAddr p j) 4

def ScalarRestPublic (s t : State) : Prop :=
 s.sp=t.sp ∧ s.gpr .x3=t.gpr .x3 ∧ (s.gpr .x4).toNat=(t.gpr .x4).toNat

theorem scalarRest_relCT {η : Nat} (hη : η=2∨η=4) :
    RelCT isa ScalarRestPublic
      (.ite (.zero .x .x4) (.block []) (.block (rbTry η))) (fun _ _=>True) := by
  have nilc : ∃h,(taint.check (Taint.ofRegs []) (.block ([] : List Instr)) h).isSome=true:=⟨_,by taint_decide⟩
  have tryc : ∃h,(taint.check (Taint.ofRegs [.x3]) (.block (rbTry η)) h).isSome=true := by
    rcases hη with rfl|rfl <;> exact ⟨_,by taint_decide⟩
  obtain ⟨_,hn⟩:=nilc
  obtain ⟨_,ht⟩:=tryc
  refine RelCT.ite (fun s t h=>by rw [eval_zero,eval_zero,eq_zero_iff,eq_zero_iff,h.2.2]) ?_ ?_
  · exact RelCT.taint (A := taint) _ (fun _ _ h=>
      VG.Proof.MlKem.AArch64.agree_of h.1.1 (fun _ hh=>False.elim (List.not_mem_nil hh))) hn
  · exact RelCT.taint (A := taint) _ (fun _ _ h=>
      VG.Proof.MlKem.AArch64.agree_of h.1.1 (fun r hr=>by
        rw [List.mem_singleton.mp hr]; exact h.1.2.1)) ht

theorem scalarLow_ok {η : Nat} (hη : η=2∨η=4) {s : State} {p : Addr} {L : List Zq} {b : Byte}
    (h : ScalarPairReady η p L b s) (hl : L.length<256) :
    WP isa (.block (rbTry η++([.lsr .x .x7 .x6 4] : List Instr))) s fun t=>
      Keep scalarPairRegs s t ∧ t.gpr .x3=coeffAddr p (hbTry η L (b.toNat%16)).length ∧
      (t.gpr .x4).toNat=256-(hbTry η L (b.toNat%16)).length := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.try_ok hη
    (by omega) h.consts h.low h.output h.remaining hl h.stored (h.write _ hl))
    fun a ⟨hk,_,h3,h4,_⟩=>?_
  refine WP.mono (scalarHigh_ok (s := a) (b := b)
    (by rw [hk.gpr .x6 (by decide)]; exact h.byte)) fun t ⟨ht,_⟩=>?_
  exact ⟨(hk.trans ht.keep).mono (by decide),by rw [ht.get .x3]; exact h3,
    by rw [ht.get .x4]; exact h4⟩

theorem scalarPair_relCT {η : Nat} (hη : η=2∨η=4) {p : Addr}
    {L M : List Zq} {b c : Byte} (hl : L.length=M.length) (hb : hbOks η b=hbOks η c) :
    RelCT isa (fun s t=>ScalarPairReady η p L b s ∧ ScalarPairReady η p M c t ∧ s.sp=t.sp)
      (scalarPair η) (fun _ _=>True) := by
  have hm : (hbTry η L (b.toNat%16)).length=(hbTry η M (c.toNat%16)).length := by
    rw [hbTry_length,hbTry_length,hl,show halfByteOk η (b.toNat%16)=halfByteOk η (c.toNat%16) from congrArg Prod.fst hb]
  have nilc : ∃h,(taint.check (Taint.ofRegs []) (.block ([] : List Instr)) h).isSome=true:=⟨_,by taint_decide⟩
  have lowc : ∃h,(taint.check (Taint.ofRegs [.x3])
      (.block (rbTry η++([.lsr .x .x7 .x6 4] : List Instr))) h).isSome=true := by
    rcases hη with rfl|rfl <;> exact ⟨_,by taint_decide⟩
  obtain ⟨_,hn⟩:=nilc
  obtain ⟨_,hc⟩:=lowc
  unfold scalarPair
  refine RelCT.ite (fun s t h=>by
    rw [remaining_zero h.1.remaining h.1.bound,remaining_zero h.2.1.remaining h.2.1.bound,hl]) ?_ ?_
  · exact RelCT.taint (A := taint) _ (fun _ _ h=>
      VG.Proof.MlKem.AArch64.agree_of h.1.2.2 (fun _ hh=>False.elim (List.not_mem_nil hh))) hn
  · refine RelCT.seq (R := ScalarRestPublic) ?_ (scalarRest_relCT hη)
    have ht := RelCT.taint (A := taint) _
      (fun s t (h : (ScalarPairReady η p L b s ∧ ScalarPairReady η p M c t ∧ s.sp=t.sp) ∧
          isa.eval (.zero .x .x4) s=some false)=>
        VG.Proof.MlKem.AArch64.agree_of h.1.2.2 (fun r hr=>by
          rw [List.mem_singleton.mp hr,h.1.1.output,h.1.2.1.output,hl])) hc
    intro s t a d u v h es et
    have he:=(ht _ _ _ _ _ _ h es et).1
    have hz:=h.2
    rw [remaining_zero h.1.1.remaining h.1.1.bound] at hz
    have hne : L.length≠256:=by simpa only [Option.some.injEq,decide_eq_false_iff_not] using hz
    have hlt : L.length<256:=by have:=h.1.1.bound; omega
    obtain ⟨_,_,ex,hu⟩:=scalarLow_ok hη h.1.1 hlt
    obtain ⟨_,_,ey,hv⟩:=scalarLow_ok hη h.1.2.1 (by rw [←hl]; exact hlt)
    obtain ⟨_,rfl⟩:=Exec.det es ex
    obtain ⟨_,rfl⟩:=Exec.det et ey
    exact ⟨he,by rw [hu.1.sp,hv.1.sp]; exact h.1.2.2,
      by rw [hu.2.1,hv.2.1,hm],by rw [hu.2.2,hv.2.2,hm]⟩

structure ScalarBodyReady (η : Nat) (p : Addr) (L : List Zq) (b : Byte) (s : State) : Prop where
 consts : ScalarConsts η s
 bound : L.length≤256
 stored : Stored s.mem p L
 output : s.gpr .x3=coeffAddr p L.length
 remaining : (s.gpr .x4).toNat=256-L.length
 byte : s.mem (s.gpr .x2)=b
 read : InRegions (s.rd++s.wr) (s.gpr .x2) 1
 write : ∀j<256,InRegions s.wr (coeffAddr p j) 4

theorem scalarLoad_ready {η : Nat} {p : Addr} {L : List Zq} {b : Byte} {s : State}
    (h : ScalarBodyReady η p L b s) :
    WP isa (.block VG.Impl.MlDsa.AArch64.Sample.rbLoad) s fun t=>
      t.sp=s.sp ∧ ScalarPairReady η p L b t := by
  refine WP.mono (scalarLoad_ok h.consts.x11 h.read) fun t ⟨hk,_,_,hb,hl⟩=>?_
  refine ⟨hk.sp,h.consts.keep hk.keep (by decide),h.bound,?_,?_,?_,?_,?_,?_⟩
  · rw [hk.mem]; exact h.stored
  · rw [hk.get .x3]; exact h.output
  · rw [hk.get .x4]; exact h.remaining
  · rw [hb,h.byte]
  · rw [hl,h.byte]
  · intro j hj; rw [hk.wr]; exact h.write j hj

theorem scalarBody_relCT {η : Nat} (hη : η=2∨η=4) {p : Addr}
    {L M : List Zq} {b c : Byte} (hl : L.length=M.length) (hb : hbOks η b=hbOks η c) :
    RelCT isa (fun s t=>ScalarBodyReady η p L b s ∧ ScalarBodyReady η p M c t ∧
        s.sp=t.sp ∧ s.gpr .x2=t.gpr .x2)
      (VG.Impl.MlDsa.AArch64.Sample.rbBody η) (fun _ _=>True) := by
  change RelCT isa _ (.seq (.block VG.Impl.MlDsa.AArch64.Sample.rbLoad) (scalarPair η)) _
  refine RelCT.seq (R := fun (s t : State)=>ScalarPairReady η p L b s ∧
    ScalarPairReady η p M c t ∧ s.sp=t.sp) ?_ (scalarPair_relCT hη hl hb)
  have hc : ∃h,(taint.check (Taint.ofRegs [.x2])
      (.block VG.Impl.MlDsa.AArch64.Sample.rbLoad) h).isSome=true:=⟨_,by taint_decide⟩
  obtain ⟨_,hc⟩:=hc
  have ht := RelCT.taint (A := taint) _
    (fun s t (h : ScalarBodyReady η p L b s ∧ ScalarBodyReady η p M c t ∧
        s.sp=t.sp ∧ s.gpr .x2=t.gpr .x2)=>
      VG.Proof.MlKem.AArch64.agree_of h.2.2.1 (fun r hr=>by
        rw [List.mem_singleton.mp hr]; exact h.2.2.2)) hc
  intro s t a d u v h es et
  have he:=(ht _ _ _ _ _ _ h es et).1
  obtain ⟨_,_,ex,hu⟩:=scalarLoad_ready h.1
  obtain ⟨_,_,ey,hv⟩:=scalarLoad_ready h.2.1
  obtain ⟨_,rfl⟩:=Exec.det es ex
  obtain ⟨_,rfl⟩:=Exec.det et ey
  exact ⟨he,hu.2,hv.2,by rw [hu.1,hv.1]; exact h.2.2.1⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
