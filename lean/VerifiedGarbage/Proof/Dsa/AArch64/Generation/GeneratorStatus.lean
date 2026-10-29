module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorPlan
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorPlan

/-! # Generator decision flags and persistent success/retry status -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem generatorTest_ok {s : State} {valid : Bool} (hr : s.gpr .x3 = mask valid) :
    eval (.zero .x .x3) s = some (!valid) := by
  cases valid <;> simp only [eval, State.read, hr, Size.bits, BitVec.setWidth_eq] <;> rfl

theorem generatorSetStatus_ok {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorMemory p W s) (status : Nat) (hs : status < 2 ^ 16) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.stackStatus status)) s fun t =>
      GeneratorMemory p (upd W 19 (BitVec.ofNat 64 status)) t ∧
      Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off p.B g) p.len = Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.B g) p.len ∧
      Frame p.changed s.mem t.mem ∧ Keep [.x3] s t := by
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
    frame kt.rd kt.wr, ?_, frame, kt⟩
  apply VG.Proof.Dsa.Generation.frame_bytesAt ff
  · intro r hr; rcases List.mem_singleton.mp hr with rfl
    exact (p.frameSeparate _ (by simp)).symm
  · rcases p.width with hh | hh | hh <;> omega

end VG.Proof.Dsa.AArch64.Generation
