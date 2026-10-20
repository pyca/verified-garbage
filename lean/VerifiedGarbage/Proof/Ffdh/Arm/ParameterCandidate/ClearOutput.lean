module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResultContext
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.ZeroBuffer
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Rejected or incomplete candidates use the existing verified FFDH byte-clear loop. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm

private theorem clearHead_ok {s : State} {dst usedPtr : BitVec 32} {n consumed : Nat}
    (h : ResultContext dst usedPtr n consumed s) :
    WP isa (.block [.ldrSp .r0 4, .ldrSp .lr 12, .mov .r2 (.imm 0)]) s fun t =>
      (t.gpr .r0 = dst ∧ t.gpr .lr = BitVec.ofNat 32 n ∧ t.gpr .r2 = 0 ∧ t.mem = s.mem) ∧
        Rest [.r0, .r2, .lr] s t := by
  have out : s.mem.readW (State.addr (s.sp + 4#32)) 32 = dst := by
    simpa only [resultValues] using h.saved.saved 4 (by simp [resultSlots])
  have count : s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 n := by
    simpa only [resultValues] using h.saved.saved 12 (by simp [resultSlots])
  refine withRest [.r0, .r2, .lr] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block [.ldrSp .r0 4, .ldrSp .lr 12, .mov .r2 (.imm 0)] : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  ffrun [BitVec.add_zero, h.saved.read (d := 4) (by decide), h.saved.read (d := 12) (by decide), out, count]

theorem clearOutput_ok {s : State} {dst usedPtr : BitVec 32} {n consumed : Nat}
    (h : ResultContext dst usedPtr n consumed s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.clearOutput s fun t =>
      ResultContext dst usedPtr n consumed t ∧ Spec.Rsa.bytesAt t.mem (State.addr dst) n = List.replicate n 0 ∧
      Frame [⟨State.addr dst, n⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.clearOutput VG.Impl.Ffdh.Arm.Domain.GenerateKey.zeros
  refine WP.seq (WP.mono (clearHead_ok h) ?_)
  rintro u ⟨⟨ptr, count, zero, memory⟩, rest⟩
  have ctx := h.after_memory memory rest
  refine WP.mono (zeroBuffer_ok false u h.positive h.countFits h.output.fits ctx.output.writable zero rfl ptr count) ?_
  rintro t ⟨bytes, _, _, changed, restT⟩
  have finalCtx := ctx.after_output changed restT
  rw [memory] at changed
  exact ⟨finalCtx, bytes, changed, (rest.mono (by simp)).trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
