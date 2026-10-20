module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
public import VerifiedGarbage.Proof.MillerRabin.X86.Context

/-! # Public geometry and registers across the prepared round's timing proof -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem round_wf_regs {s : State} {rs out : List Reg} {f g : Bool}
    (h : VG.X86.Taint.Wf (roundTaint rs f) s) : VG.X86.Taint.Wf (roundTaint out g) s :=
  ⟨h.lens, h.bases, h.wbases, h.args, h.argBases, h.stk, h.frames, h.room⟩

theorem round_republish {s t : State} {rs out : List Reg} {f g : Bool}
    (h : VG.X86.Taint.Agree (roundTaint rs f) s t)
    (rf : VG.X86.Taint.AgreeRF (roundTaint out g).regs g s t) :
    VG.X86.Taint.Agree (roundTaint out g) s t :=
  ⟨rf, h.wr, round_wf_regs h.wf₁, round_wf_regs h.wf₂, h.ok, h.slots, h.sp, h.argMem⟩

def Pair (g : Geometry) (rs : List Reg) (s t : State) : Prop :=
  Context g s ∧ Context g t ∧ VG.X86.Taint.Agree (roundTaint rs) s t

theorem round_regs {s t : State} {rs : List Reg}
    (H : VG.X86.Taint.Agree (roundTaint rs) s t) {r : Reg} (mem : r ∈ rs) :
    s.gpr r = t.gpr r := H.rf.1 r (by
  simp only [roundTaint, RegSet.mem_ofList]
  exact List.mem_cons_of_mem _ mem)

theorem round_forget {s t : State} {rs : List Reg}
    (H : VG.X86.Taint.Agree (roundTaint rs) s t) : VG.X86.Taint.Agree (roundTaint []) s t := by
  refine round_republish H ⟨?_, fun h => nomatch h⟩
  intro r mem
  simp only [roundTaint, RegSet.mem_ofList, List.mem_singleton] at mem
  subst r
  exact H.rf.1 .esp (by simp only [roundTaint, RegSet.mem_ofList]; exact List.mem_cons_self)

theorem round_add_regs {s t : State} {rs : List Reg}
    (H : VG.X86.Taint.Agree (roundTaint []) s t)
    (regs : ∀ r ∈ rs, s.gpr r = t.gpr r) : VG.X86.Taint.Agree (roundTaint rs) s t := by
  refine round_republish H ⟨?_, fun h => nomatch h⟩
  intro r mem
  simp only [roundTaint, RegSet.mem_ofList, List.mem_cons] at mem
  rcases mem with rfl | mem
  · exact H.rf.1 .esp (by simp only [roundTaint, RegSet.mem_ofList]; exact List.mem_cons_self)
  · exact regs r mem

theorem pair_regs {g : Geometry} {s t : State} {before after : List Reg}
    (H : Pair g before s t) (subset : ∀ r ∈ after, r ∈ before) : Pair g after s t :=
  ⟨H.1, H.2.1, round_add_regs (round_forget H.2.2) fun r mem => round_regs H.2.2 (subset r mem)⟩

end VG.Proof.MillerRabin.X86
