import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParseSetup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParserTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

structure CoreReady (η : Nat) (table p q : Addr) (L : List Zq) (X : List Byte) (s : State) : Prop where
 bound : L.length≤256
 bytes : X.length=272
 vectorLayout : Layout s table p q X
 scalarLayout : ScalarLayout s p q X
 tableMem : TableAt s.mem table
 stored : Stored s.mem p L
 input : s.gpr .x2=q
 output : s.gpr .x3=p
 count : s.gpr .x4=BitVec.ofNat 64 (256-L.length)
 tableAddr : s.gpr .x19+6000=table

theorem parseSetup_taint {η : Nat} (hη : η=2∨η=4) : ∃hint,
    (taint.check (Taint.ofRegs []) (.block (parseSetup η)) hint).isSome=true :=
  by rcases hη with rfl|rfl <;> exact ⟨_,by taint_decide⟩

theorem parseCore_relCT {η : Nat} (hη : η=2∨η=4) {table p q : Addr}
    {L M : List Zq} {X Y : List Byte} (hl : L.length=M.length)
    (hx : X.map (hbOks η)=Y.map (hbOks η)) :
    RelCT isa (fun s t=>CoreReady η table p q L X s ∧ CoreReady η table p q M Y t ∧ s.sp=t.sp)
      (parseCore η) (fun _ _=>True) := by
  obtain ⟨_,hc⟩:=parseSetup_taint hη
  have cs : RelCT isa (fun s t=>s.sp=t.sp) (.block (parseSetup η)) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ hh=>VG.Proof.MlKem.AArch64.agree_of hh
      (fun _ hr=>False.elim (List.not_mem_nil hr))) hc
  intro s t tr ur u v h es et
  cases es with | seq es0 es1 =>
    cases et with | seq et0 et1 =>
      have he:=(cs _ _ _ _ _ _ h.2.2 es0 et0).1
      obtain ⟨_,_,ex,ha⟩:=parseSetup_inv hη h.1.bound h.1.bytes h.1.tableMem h.1.stored
        h.1.input h.1.output h.1.count h.1.tableAddr
      obtain ⟨_,_,ey,hb⟩:=parseSetup_inv hη h.2.1.bound h.2.1.bytes h.2.1.tableMem h.2.1.stored
        h.2.1.input h.2.1.output h.2.1.count h.2.1.tableAddr
      obtain ⟨_,rfl⟩:=Exec.det es0 ex
      obtain ⟨_,rfl⟩:=Exec.det et0 ey
      have hp : TranscriptPair _ _ η table p q L M X Y :=
        ⟨h.1.vectorLayout.keep ha.1 ha.2.1,h.2.1.vectorLayout.keep hb.1 hb.2.1,
          by rw [ha.1.sp,hb.1.sp]; exact h.2.2,hl,hx⟩
      have ht:=(parsedPhase_relCT hη hp
        (h.1.scalarLayout.keep ha.1 ha.2.1) (h.2.1.scalarLayout.keep hb.1 hb.2.1)
        h.1.bound _ _ _ _ _ _ ⟨ha.2.2,hb.2.2⟩ es1 et1).1
      exact ⟨by rw [he,ht],trivial⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
