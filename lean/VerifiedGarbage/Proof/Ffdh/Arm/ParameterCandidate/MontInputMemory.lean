module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontPrepare
public import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Read-only native argument loads retain the existing Montgomery preparation contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm

theorem MontPrepInput.after_memory {s t : State} {base src : BitVec 32} {capacity k : Nat} {rs : List Reg}
    (h : MontPrepInput base src capacity k s) (memory : t.mem = s.mem) (rest : Rest rs s t) :
    MontPrepInput base src capacity k t := by
  refine ⟨h.workspace.congr rest.wr, ?_, h.minLength, h.maxLength, h.space, h.sourceFits,
    by rw [rest.rd, rest.wr]; exact h.readable, h.separate,
    by rw [memory]; exact h.large, by rw [memory]; exact h.odd⟩
  have frame : Frame [⟨State.addr base, 8 * capacity⟩] s.mem t.mem := by rw [memory]; exact Frame.refl _ _
  simpa only [memory, rest.sp] using h.stack.after_workspace frame rest

theorem MontPrepInput.prepare_input {s : State} {base src : BitVec 32} {capacity k : Nat}
    (h : MontPrepInput base src capacity k s) (ptr : s.gpr .r0 = base) (count : s.gpr .r6 = BitVec.ofNat 32 k) :
    PrepareInput base src capacity k s :=
  ⟨h.workspace, h.stack, ptr, count, h.minLength, h.maxLength, h.space, h.sourceFits, h.readable, h.separate, h.large, h.odd⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
