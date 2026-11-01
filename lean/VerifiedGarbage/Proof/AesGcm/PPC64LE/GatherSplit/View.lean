module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.Callee
import VerifiedGarbage.Proof.AesGcm.ScratchGather

-- separate module: identify the caller's buffers in the callee's contract.
/-! # The split-seal call's argument view -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.GatherSplit
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.Gather

abbrev sourceRegion (s e : State) : Region := ⟨e.mem.readW (Src s) 64,(firstLen e).toNat⟩
abbrev outgoingRegion (s : State) : Region := ⟨Pf s+96,24⟩

def callRead (s e : State) : List Region := [cR s,nR s,aR s,sourceRegion s e,outgoingRegion s]
def callWrite (s : State) : List Region := [dR s,tgR s]
def callView (s e c : State) : State := c.callEntry.withRegions (callRead s e) (callWrite s)


theorem source_listed {s e : State} (h : Gather.Lay s) (he : Gather.Entered s e) (hc : 0<Cnt s) :
    sourceRegion s e∈lsR s := by
  have hp := first_listed (gatherPre_of h he) hc
  obtain ⟨hls,-⟩ := Proof.AesGcm.listed_congr_le (Nat.le_refl _) h.hag
  rw [← he.mem] at hls
  rw [hls] at hp
  exact hp


theorem Prepared.view_gpr {s e c : State} (hc : Prepared s e c) {r : Reg}
    (hr : r∈[Reg.r3,.r4,.r5,.r6,.r7,.r8]) : (callView s e c).gpr r=s.gpr r := by
  have hn : ∀ r∈[Reg.r3,.r4,.r5,.r6,.r7,.r8],r∉linkRegs := by decide
  change c.callEntry.gpr r=s.gpr r
  rw [State.callEntry_gpr c (hn r hr)]
  exact hc.regs r hr


theorem Prepared.view_arg {s e c : State} (hc : Prepared s e c) {j : Nat} (hj : j<3) :
    stackArg (callView s e c) j=stackArg s j := by
  change c.mem.readW (c.sp+BitVec.ofNat 64 (32+8*(8+j))) 64=stackArg s j
  rw [hc.sp,show 32+8*(8+j)=96+8*j by omega]
  exact hc.args j hj


theorem Prepared.view_regions {s e c : State} (hc : Prepared s e c) :
    callContext (callView s e c)=cR s ∧ callNonce (callView s e c)=nR s ∧
    callAad (callView s e c)=aR s ∧ callSource (callView s e c)=sourceRegion s e ∧
    callData (callView s e c)=dR s ∧ callTag (callView s e c)=tgR s ∧
    callArgsRegion (callView s e c)=outgoingRegion s := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · unfold callContext
    rw [hc.view_gpr (by decide)]
  · unfold callNonce
    rw [hc.view_gpr (by decide),hc.view_gpr (by decide)]
  · unfold callAad
    rw [hc.view_gpr (by decide),hc.view_gpr (by decide)]
  · change (⟨c.callEntry.gpr .r9,(c.callEntry.gpr .r10).toNat⟩ : Region)=_
    rw [State.callEntry_gpr c (by decide),State.callEntry_gpr c (by decide),hc.source,hc.length]
  · unfold callData
    rw [hc.view_arg (by decide),hc.view_arg (by decide)]
  · unfold callTag
    rw [hc.view_arg (by decide)]
  · change (⟨c.sp+BitVec.ofNat 64 (32+8*(8+0)),24⟩ : Region)=_
    rw [hc.sp]
    rfl

end VG.Proof.AesGcm.PPC64LE.GatherSplit
