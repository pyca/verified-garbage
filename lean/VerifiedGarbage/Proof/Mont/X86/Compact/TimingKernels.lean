module

public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingBase
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Mont.X86.Rt.Zero
public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub
public import VerifiedGarbage.Proof.Mont.X86.Compact.Select

/-! # The native-word loops have public addresses and public bounds -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Dsa.X86

theorem modulusSubPtr_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint []))
    (.block (Compact.arrayPtr .esi 0)) (VG.X86.Taint.Agree (timingTaint [])) :=
  checkedBlockInvariant rfl rfl

theorem outSelectPtr_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint []))
    (.block (Compact.operandPtr .esi 2 .edx)) (VG.X86.Taint.Agree (timingTaint [])) :=
  checkedBlockInvariant (τ' := timingTaint [.edx] true) rfl rfl

theorem zeroLength_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint []))
    (.block (Compact.lenTimes .esi .eax 1)) (VG.X86.Taint.Agree (timingTaint [])) :=
  checkedBlockInvariant (τ' := timingTaint [.eax] false) rfl rfl

theorem rowLength_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint []))
    (.block (Compact.lenTimes .esi .eax 0)) (VG.X86.Taint.Agree (timingTaint [])) :=
  checkedBlockInvariant (τ' := timingTaint [.eax] false) rfl rfl

theorem byteLength_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint []))
    (.block (Compact.lenTimes .eax .edx 0)) (VG.X86.Taint.Agree (timingTaint [])) :=
  checkedBlockInvariant (τ' := timingTaint [.edx] false) rfl rfl

theorem outputLength_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint []))
    (.block (Compact.lenTimes .edi .eax 0)) (VG.X86.Taint.Agree (timingTaint [])) :=
  checkedBlockInvariant (τ' := timingTaint [.eax] false) rfl rfl

theorem redDigit_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint [.edi, .ebp]))
    (.block Compact.redDigit) (VG.X86.Taint.Agree (timingTaint [.edi, .ebp])) :=
  checkedBlockInvariant rfl rfl

theorem carryWords_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint [.ebp, .edi]))
    (.block Rt.carryWords) (VG.X86.Taint.Agree (timingTaint [.ebp, .edi])) :=
  checkedBlockInvariant rfl rfl

theorem mask_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint [.ebp, .edi]))
    (.block Rt.mask) (VG.X86.Taint.Agree (timingTaint [.ebp, .edi])) :=
  checkedBlockInvariant rfl rfl

theorem restore_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint []))
    (.block Compact.restoreRegs) (VG.X86.Taint.Agree (timingTaint [])) :=
  checkedBlockInvariant rfl rfl

theorem zeroLoop_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint [.ebp, .esi]))
    (.loop (.block VG.Proof.Mont.X86.Rt.zeroBody) .ne)
    (VG.X86.Taint.Agree (timingTaint [.ebp, .esi])) :=
  checkedProgramChange (τ' := timingTaint [.ebp, .esi] true)
    (hint := VG.Taint.hintOf taint (timingTaint [.ebp, .esi])
      (.loop (.block VG.Proof.Mont.X86.Rt.zeroBody) .ne)) rfl rfl

theorem pairLoop_relCT_raw : RelCT isa (VG.X86.Taint.Agree (timingTaint [.edi, .ebp, .ecx, .esi]))
    (.loop (.block Rt.pairStep) .ne)
    (VG.X86.Taint.Agree (timingTaint [.edi, .ebp, .ecx, .esi])) :=
  checkedProgramChange (τ' := timingTaint [.edi, .ebp, .ecx, .esi] true)
    (hint := VG.Taint.hintOf taint (timingTaint [.edi, .ebp, .ecx, .esi])
      (.loop (.block Rt.pairStep) .ne)) rfl rfl

theorem subLoop_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint [.ebp, .esi, .ebx, .edi]))
    (.loop (.block VG.Proof.Mont.X86.Rt.subBody) .ne)
    (VG.X86.Taint.Agree (timingTaint [.ebp, .esi, .ebx, .edi])) :=
  checkedProgramChange (τ' := timingTaint [.edx, .ebp, .esi, .ebx, .edi] true)
    (hint := VG.Taint.hintOf taint (timingTaint [.ebp, .esi, .ebx, .edi])
      (.loop (.block VG.Proof.Mont.X86.Rt.subBody) .ne)) rfl rfl

theorem selectLoop_relCT : RelCT isa (VG.X86.Taint.Agree (timingTaint [.ebp, .esi, .edi]))
    (.loop (.block selBody) .ne) (VG.X86.Taint.Agree (timingTaint [.ebp, .esi, .edi])) :=
  checkedProgramChange (τ' := timingTaint [.ebp, .esi, .edi] true)
    (hint := VG.Taint.hintOf taint (timingTaint [.ebp, .esi, .edi]) (.loop (.block selBody) .ne)) rfl rfl

end VG.Proof.Mont.X86.Compact
