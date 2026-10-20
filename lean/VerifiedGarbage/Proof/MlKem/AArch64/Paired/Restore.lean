module

public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Saved
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

/-! # Restore the sampler caller while retaining its accumulated success flag -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64

/-- Registers that may change across one complete paired matrix sample. -/
def pairRegs : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x24]

def pairWorkingRegs : List Reg := pairRegs++Impl.MlKem.AArch64.Paired.saved

theorem restored_keep {initial s t : State} (h : Keep pairWorkingRegs initial s)
    (ht : Only Impl.MlKem.AArch64.Paired.saved s t)
    (hr : ∀r∈Impl.MlKem.AArch64.Paired.saved,t.gpr r=initial.gpr r) :
    Keep pairRegs initial t := by
  refine ⟨?_,ht.rd.trans h.rd,ht.wr.trans h.wr,ht.sp.trans h.sp,
    fun r hp => (ht.vcs r hp).trans (h.vcs r hp)⟩
  intro r hn
  by_cases hs : r∈Impl.MlKem.AArch64.Paired.saved
  · exact hr r hs
  · rw [ht.get r hs,h.get r (by simp only [pairWorkingRegs,List.mem_append,not_or]; exact ⟨hn,hs⟩)]

/-- The restore block does not disturb either the sampled polynomials or x24. -/
theorem restore_ok {initial s : State} {p : Addr}
    (h : Keep pairWorkingRegs initial s) (hp : s.gpr .x19=p)
    (sv : Noise.Saved p initial s.mem) (hc : Covers [⟨p,2048⟩] s.wr) :
    WP isa (.block (Impl.MlKem.AArch64.Paired.saved.zipIdx.reverse.map fun (r,i)=>
      .ldr .x r .x19 (1800+8*i))) s fun t =>
      Keep pairRegs initial t ∧ t.mem=s.mem ∧ t.gpr .x24=s.gpr .x24 := by
  refine WP.mono (Noise.restores_ok hp sv (fun i hi=>?_)) fun t ⟨ht,hr⟩ =>
    ⟨restored_keep h ht hr,ht.mem,ht.get .x24 (by decide)⟩
  exact in_rd_wr (rd:=s.rd) (Noise.inScratch hc (by omega) (by decide))

end VG.Proof.MlKem.AArch64.Paired
