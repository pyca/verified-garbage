module

import VerifiedGarbage.Proof.Mont.X86.Compact.TimingFront
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingFinish
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingKernels
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingLift

/-! # The complete prepared Montgomery core has a public trace -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Impl.Mont.X86

theorem unassoc {P Q : State → State → Prop} {a b c : Prog isa}
    (H : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s t tr ur u z hp E G
  cases E with
  | seq ab₁ c₁ =>
    cases ab₁ with
    | seq a₁ b₁ =>
      cases G with
      | seq ab₂ c₂ =>
        cases ab₂ with
        | seq a₂ b₂ =>
          obtain ⟨trace, R⟩ := H _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          exact ⟨by simpa only [List.append_assoc] using trace, R⟩

theorem core_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g []) Compact.core
      (VG.X86.Taint.Agree (timingTaint [.ebp, .esi, .edi])) := by
  unfold Compact.core
  exact RelCT.assoc (RelCT.assoc (RelCT.seq (unassoc (front_relCT v))
    (RelCT.seq (subM_relCT v) (finish_trace v))))

theorem inner_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g []) (.seq Compact.core (.block Compact.restoreRegs))
      (VG.X86.Taint.Agree (timingTaint [])) :=
  RelCT.seq (core_trace v) (restore_relCT.mono (fun _ _ H => timing_forget H) (fun _ _ H => H))

end VG.Proof.Mont.X86.Compact
