import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedRestoreLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlKem.AArch64 (Keep)

def lowKernel (g : Nat) : Prog isa :=
  .seq (.loop (.block (finalLowCode g++finalAdvance)) (.nonzero .x .x12))
    (.block (finish .r0))

/-- Exact final inverse/check traversal followed by return and ABI restore. -/
theorem lowKernel_ok (g : Nat) (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) {s₀ s : State} {table work : Addr}
    {gr : List Reg} {vr : List VReg}
    (hf : CallFrame gr vr s₀ s) (hs : Saved s.mem work s₀.v)
    (hwork : s.gpr .x2=work)
    (hsd : (⟨work+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hrs : ∀p∈extraSlots 1920,InRegions (s.rd++s.wr)
      ((work+BitVec.ofNat 64 128)+BitVec.ofNat 64 p.2) 16)
    (hsda : (⟨work+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x16,2048⟩)
    (ht : PairedTable.Words s.mem table)
    (hd : (⟨table,4096⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hda : (⟨table,4096⟩:Region).Disjoint ⟨s.gpr .x16,2048⟩)
    (hx : s.gpr .x1=table+BitVec.ofNat 64 3840)
    (hcount : s.gpr .x12=8) (hc : LowReady g s)
    (hrt : ∀off,off+16≤4096 → InRegions (s.rd++s.wr) (table+BitVec.ofNat 64 off) 16)
    (hr : ∀u<8,∀p:Fin 2,∀j:Fin 8,InRegions (s.rd++s.wr)
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (hw : ∀u<8,∀i:LowIndex,
      InRegions (s.rd++s.wr) ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions (s.rd++s.wr) ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr ((s.gpr .x16+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr ((s.gpr .x16+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i+128)) 16) :
    WP isa (lowKernel g) s fun t =>
      let d := lowPassData g work (s.gpr .x15) (s.gpr .x16) (lowConstantsAt s) (dataAt s) 8
      Keep ((gr++finalGprs)++([.x0,.x9,.x10] : List Reg)) s₀ t ∧
      t.mem=d.mem ∧ t.gpr .x0=dataReturn .r0 d := by
  unfold lowKernel
  refine loop_finish_ok _ hf hs (vs := lowRunRegs) (writes := [⟨s.gpr .x15,2048⟩,⟨s.gpr .x16,2048⟩])
    (by intro r hr; rcases List.mem_cons.mp hr with rfl | hr; exact hsd;
        have he := List.mem_singleton.mp hr; subst r; exact hsda) hrs ?_
  refine WP.mono (lowLoop_ok hg ht hd hda hx hcount hc hrt hr hw)
    fun t ⟨hft,h2,_,_,hdata⟩ => ?_
  refine ⟨hft,by simpa only [hwork,show (128:Addr)=BitVec.ofNat 64 128 by rfl] using h2,by simpa only [hwork] using hdata,?_⟩
  change Frame _ _ (dataAt t).mem
  rw [hdata]
  exact lowPass_frame _ _ _ _ _ _ (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
