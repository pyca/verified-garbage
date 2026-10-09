import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedRestoreLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlKem.AArch64 (Keep)

def finalKernel (hint : Bool) : Prog isa :=
  .seq (.loop (.block (finalCheckCode hint++finalAdvance)) (.nonzero .x .x12))
    (.block (finish (if hint then .h else .z)))

/-- Exact final inverse/check traversal followed by return and ABI restore. -/
theorem finalKernel_ok (hint : Bool) {s₀ s : State} {table work : Addr}
    {gr : List Reg} {vr : List VReg}
    (hf : CallFrame gr vr s₀ s) (hs : Saved s.mem work s₀.v)
    (hwork : s.gpr .x2=work)
    (hsd : (⟨work+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hrs : ∀p∈extraSlots 1920,InRegions (s.rd++s.wr)
      ((work+BitVec.ofNat 64 128)+BitVec.ofNat 64 p.2) 16)
    (ht : PairedTable.Words s.mem table)
    (hd : (⟨table,4096⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hx : s.gpr .x1=table+BitVec.ofNat 64 3840)
    (hcount : s.gpr .x12=8) (hc : CheckReady hint s)
    (hrt : ∀off,off+16≤4096 → InRegions (s.rd++s.wr) (table+BitVec.ofNat 64 off) 16)
    (hr : ∀u<8,∀p:Fin 2,∀j:Fin 8,InRegions (s.rd++s.wr)
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (hw : ∀u<8,∀p:Fin 2,∀j:Fin 8,
      InRegions (s.rd++s.wr) ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16 ∧
      (hint=true → InRegions (s.rd++s.wr) ((s.gpr .x16+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16) ∧
      InRegions s.wr ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16) :
    WP isa (finalKernel hint) s fun t =>
      let d := finalPassData hint work (s.gpr .x15) (s.gpr .x16) (constantsAt s) (dataAt s) 8
      Keep ((gr++finalGprs)++([.x0,.x9,.x10] : List Reg)) s₀ t ∧
      t.mem=d.mem ∧ t.gpr .x0=dataReturn (if hint then .h else .z) d := by
  unfold finalKernel
  refine loop_finish_ok _ hf hs (vs := finalCheckRegs) (writes := [⟨s.gpr .x15,2048⟩])
    (by simpa only [List.mem_singleton,forall_eq] using hsd) hrs ?_
  refine WP.mono (finalLoop_ok hint ht hd hx hcount hc hrt hr hw)
    fun t ⟨hft,h2,_,_,hdata⟩ => ?_
  refine ⟨hft,by simpa only [hwork,show (128:Addr)=BitVec.ofNat 64 128 by rfl] using h2,by simpa only [hwork] using hdata,?_⟩
  change Frame _ _ (dataAt t).mem
  rw [hdata]
  exact finalPass_frame _ _ _ _ _ _ (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
