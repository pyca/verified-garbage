module
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorPlan
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.Memory

/-! # Generator decision flags and persistent success/retry status -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem generatorTest_ok {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State}
    {valid : Bool} (h : GeneratorMemory p W s) (hr : s.gpr .rax = mask valid) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) s fun t =>
      t.zf = some (!valid) ∧ GeneratorMemory p W t ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (!valid) ∧ t.mem = s.mem) (by
    xrun [hr]
    cases valid <;> decide) rfl) fun t ⟨⟨hz, hm⟩, kt⟩ => ?_
  obtain ⟨V, R⟩ := h.rep
  have Rt : Rep t.mem p.F p.S V W := hm ▸ R
  have Lt := lay_of_rep h.layout R Rt rfl (kt.gpr (by decide)) kt.2.2
  exact ⟨hz, h.frame Lt ⟨V, Rt⟩ h.base h.input (by rw [hm]; exact Frame.refl _ _)
    kt.2.1 kt.2.2, hm, kt⟩

theorem generatorSetStatus_ok {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorMemory p W s) (status : Nat) (hs : status < 2 ^ 32) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.stackStatus status)) s fun t =>
      GeneratorMemory p (upd W 19 (BitVec.ofNat 64 status)) t ∧
      Spec.Rsa.bytesAt t.mem (off p.B g) p.len = Spec.Rsa.bytesAt s.mem (off p.B g) p.len ∧
      Frame p.changed s.mem t.mem ∧ Keep [.rax] s t := by
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (stackStatus_ok h.layout R status hs) fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame [⟨p.F, frameBytes⟩] s.mem t.mem := by
    intro a ha
    apply ft a
    right
    have hn := ha ⟨p.F, frameBytes⟩ (by simp)
    change ¬ ofs p.F a < frameBytes at hn
    unfold frameBytes at hn
    omega
  have frame : Frame p.changed s.mem t.mem := ff.mono (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [GeneratorPlan.changed])
  refine ⟨h.frame Lt ⟨V, Rt⟩ (by simpa [upd] using h.base) (by simpa [upd] using h.input)
    frame kt.2.1 kt.2.2, ?_, frame, kt⟩
  apply VG.Proof.Dsa.Generation.frame_bytesAt ff
  · intro r hr; rcases List.mem_singleton.mp hr with rfl
    exact (p.frameSeparate _ (by simp)).symm
  · rcases p.width with hh | hh | hh <;> omega

end VG.Proof.Dsa.X86_64.Generation
