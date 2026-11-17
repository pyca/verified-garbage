module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! ### `MillerRabin.X86.TimingBlocks`, which this module and modules that import it used -/

section

/-! # Secret digit and flag arithmetic has no secret-dependent trace -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

/-- Only explicitly listed registers and the stack pointer are public.
Workspace metadata is republished from its correctness invariant after loads. -/
def roundTaint (rs : List Reg := []) (flags : Bool := false) : VG.X86.Taint.T :=
  { regs := .ofList (.esp :: rs), flags := flags }

theorem squareFlag_relCT : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block squareFlag) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  checkedBlockInvariant (τ' := roundTaint [.edi]) rfl rfl

theorem windowEnd_relCT : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block windowEnd) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  checkedBlockInvariant (τ' := roundTaint [.edi]) rfl rfl

theorem maskIndex_relCT (j : Nat) : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block (maskIndex j)) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (maskIndex j)) (.block (maskIndex 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

end VG.Proof.MillerRabin.X86

end

end

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

end VG.Proof.MillerRabin.X86
