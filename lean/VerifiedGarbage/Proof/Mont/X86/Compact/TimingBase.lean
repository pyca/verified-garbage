module

public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Public argument reads inside the compact register-saving frame -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Dsa.X86

/-- The saved registers remain secret. Only the five cdecl arguments above
that frame are public; `rs` describes additional public working registers. -/
def timingTaint (rs : List Reg := []) (flags : Bool := false) : VG.X86.Taint.T :=
  { regs := .ofList (.esp :: rs), flags := flags, argLen := 24, stk := [some 16] }

theorem timing_wf_regs {s : State} {rs out : List Reg} {f g : Bool}
    (h : VG.X86.Taint.Wf (timingTaint rs f) s) : VG.X86.Taint.Wf (timingTaint out g) s :=
  ⟨h.lens, h.bases, h.wbases, h.args, h.argBases, h.stk, h.frames, h.room⟩

theorem timing_republish {s t : State} {rs out : List Reg} {f g : Bool}
    (h : VG.X86.Taint.Agree (timingTaint rs f) s t)
    (rf : VG.X86.Taint.AgreeRF (timingTaint out g).regs g s t) :
    VG.X86.Taint.Agree (timingTaint out g) s t :=
  ⟨rf, h.wr, timing_wf_regs h.wf₁, timing_wf_regs h.wf₂, h.ok, h.slots, h.sp, h.argMem⟩

theorem scratchPtr_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint []))
    (.block Compact.scratchPtr) (VG.X86.Taint.Agree (timingTaint [])) :=
  checkedBlockInvariant rfl rfl

theorem modulusPtr_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint []))
    (.block (Compact.arrayPtr .ecx 0)) (VG.X86.Taint.Agree (timingTaint [])) :=
  checkedBlockInvariant rfl rfl

theorem leftPtr_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint []))
    (.block (Compact.operandPtr .ecx 3 .edx)) (VG.X86.Taint.Agree (timingTaint [])) :=
  checkedBlockInvariant (τ' := timingTaint [.edx] true) rfl rfl

theorem rightPtr_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint []))
    (.block (Compact.operandPtr .ecx 4 .edx)) (VG.X86.Taint.Agree (timingTaint [])) :=
  checkedBlockInvariant (τ' := timingTaint [.edx] true) rfl rfl

theorem outPtr_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint []))
    (.block (Compact.operandPtr .ebx 2 .edx)) (VG.X86.Taint.Agree (timingTaint [])) :=
  checkedBlockInvariant (τ' := timingTaint [.edx] true) rfl rfl

end VG.Proof.Mont.X86.Compact
