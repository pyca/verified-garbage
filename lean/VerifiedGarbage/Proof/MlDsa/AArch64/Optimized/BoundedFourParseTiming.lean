import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourCoreTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParseTrace
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParse

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

structure ParseReady (k off : Nat) (table p q a : Addr) (L : List Zq) (X : List Byte) (s : State) : Prop where
 bound : L.length≤256
 bytes : X.length=272
 vectorLayout : Layout s table p q X
 scalarLayout : ScalarLayout s p q X
 tableMem : TableAt s.mem table
 stored : Stored s.mem p L
 input : s.gpr .x19+BitVec.ofNat 64 (840+544*k+off)=q
 output : s.gpr .x21+BitVec.ofNat 64 (1024*k)=p
 countAddr : s.gpr .x19+BitVec.ofNat 64 (7904+8*k)=a
 tableAddr : s.gpr .x19+6000=table
 count : s.mem.readW a 64=BitVec.ofNat 64 (256-L.length)
 read : InRegions (s.rd++s.wr) a 8

theorem parseAddress_ready {η k off : Nat} (hk : k<4) (ho : off≤272)
    {table p q a : Addr} {L : List Zq} {X : List Byte} {s : State}
    (h : ParseReady k off table p q a L X s) :
    WP isa (.block (parseAddress k off)) s fun t=>
      VG.Proof.MlKem.AArch64.Only [.x2,.x3,.x4] s t ∧ CoreReady η table p q L X t := by
  refine WP.mono (parseAddress_ok hk ho (by rw [h.countAddr]; exact h.read)) fun t ⟨ht,h2,h3,h4⟩=>?_
  refine ⟨ht,h.bound,h.bytes,h.vectorLayout.keep ht.keep ht.mem,
    h.scalarLayout.keep ht.keep ht.mem,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.mem]; exact h.tableMem
  · rw [ht.mem]; exact h.stored
  · rw [h2]; exact h.input
  · rw [h3]; exact h.output
  · rw [h4,h.countAddr,h.count]
  · rw [ht.get .x19]; exact h.tableAddr

theorem parseAddress_taint {k off : Nat} (hk : k<4) (ho : off=0∨off=272) : ∃h,
    (taint.check (Taint.ofRegs [.x19,.x21]) (.block (parseAddress k off)) h).isSome=true := by
  rcases (show k=0∨k=1∨k=2∨k=3 by omega) with rfl|rfl|rfl|rfl <;>
    rcases ho with rfl|rfl <;> exact ⟨_,by taint_decide⟩

theorem parseStore_taint {k : Nat} (hk : k<4) : ∃h,
    (taint.check (Taint.ofRegs [.x19]) (.block [.str .x .x4 .x19 (7904+8*k)]) h).isSome=true := by
  rcases (show k=0∨k=1∨k=2∨k=3 by omega) with rfl|rfl|rfl|rfl <;> exact ⟨_,by taint_decide⟩

theorem parseModel_relCT {η k off : Nat} (hη : η=2∨η=4) (hk : k<4) (ho : off=0∨off=272)
    {table p q a : Addr} {L M : List Zq} {X Y : List Byte}
    (hl : L.length=M.length) (hx : X.map (hbOks η)=Y.map (hbOks η)) :
    RelCT isa (fun s t=>ParseReady k off table p q a L X s ∧ ParseReady k off table p q a M Y t ∧
      s.sp=t.sp ∧ s.gpr .x19=t.gpr .x19 ∧ s.gpr .x21=t.gpr .x21)
      (parseModel η k off) (fun _ _=>True) := by
  obtain ⟨_,ha⟩:=parseAddress_taint hk ho
  obtain ⟨_,hz⟩:=parseStore_taint hk
  have ca : RelCT isa (fun (s t : State)=>s.sp=t.sp ∧ s.gpr .x19=t.gpr .x19 ∧ s.gpr .x21=t.gpr .x21)
      (.block (parseAddress k off)) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>VG.Proof.MlKem.AArch64.agree_of h.1 (fun r hr=>by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact h.2.1
      · exact h.2.2)) ha
  have cz : RelCT isa (fun (s t : State)=>s.sp=t.sp ∧ s.gpr .x19=t.gpr .x19)
      (.block [.str .x .x4 .x19 (7904+8*k)]) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>VG.Proof.MlKem.AArch64.agree_of h.1 (fun r hr=>by
      rw [List.mem_singleton.mp hr]; exact h.2)) hz
  intro s t tr ur u v h es et
  cases es with | seq es0 es1 =>
    cases es1 with | seq es1 es2 =>
      cases et with | seq et0 et1 =>
        cases et1 with | seq et1 et2 =>
          have e0:=(ca _ _ _ _ _ _ h.2.2 es0 et0).1
          obtain ⟨_,_,ex,sa⟩:=parseAddress_ready (η := η) hk (by omega) h.1
          obtain ⟨_,_,ey,ta⟩:=parseAddress_ready (η := η) hk (by omega) h.2.1
          obtain ⟨_,rfl⟩:=Exec.det es0 ex
          obtain ⟨_,rfl⟩:=Exec.det et0 ey
          have hs : _ := sa.2
          have ht : _ := ta.2
          have hsp : _ := sa.1.sp.trans (h.2.2.1.trans ta.1.sp.symm)
          have e1:=(parseCore_relCT hη hl hx _ _ _ _ _ _ ⟨hs,ht,hsp⟩ es1 et1).1
          obtain ⟨_,_,ex,hb⟩:=parseCore_ok hη hs.bound hs.bytes hs.vectorLayout hs.scalarLayout
            hs.tableMem hs.stored hs.input hs.output hs.count hs.tableAddr
          obtain ⟨_,_,ey,hc⟩:=parseCore_ok hη ht.bound ht.bytes ht.vectorLayout ht.scalarLayout
            ht.tableMem ht.stored ht.input ht.output ht.count ht.tableAddr
          obtain ⟨_,rfl⟩:=Exec.det es1 ex
          obtain ⟨_,rfl⟩:=Exec.det et1 ey
          have e2:=(cz _ _ _ _ _ _ ⟨by rw [hb.1.sp,hc.1.sp]; exact hsp,
            by rw [hb.1.gpr .x19 (by decide),hc.1.gpr .x19 (by decide),sa.1.get .x19,ta.1.get .x19]; exact h.2.2.2.1⟩ es2 et2).1
          exact ⟨by rw [e0,e1,e2],trivial⟩

theorem parse_relCT {η k off : Nat} (hη : η=2∨η=4) (hk : k<4) (ho : off=0∨off=272)
    {table p q a : Addr} {L M : List Zq} {X Y : List Byte}
    (hl : L.length=M.length) (hx : X.map (hbOks η)=Y.map (hbOks η)) :
    RelCT isa (fun s t=>ParseReady k off table p q a L X s ∧ ParseReady k off table p q a M Y t ∧
      s.sp=t.sp ∧ s.gpr .x19=t.gpr .x19 ∧ s.gpr .x21=t.gpr .x21)
      (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parse true η k off) (fun _ _=>True) := by
  intro _ _ _ _ _ _ h es et
  exact parseModel_relCT hη hk ho hl hx _ _ _ _ _ _ h (parse_exec_model es) (parse_exec_model et)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
