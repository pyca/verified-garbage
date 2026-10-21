module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeContext
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeFirst
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Omega

/-! First-octet shaping preserves all other copied bytes and saved arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

theorem shapeTop_ok (s : State) {dst src : BitVec 32} {bs : List Byte} {bits j : Nat}
    (h : ShapeContext dst src bs bits s) (bound : j < 8)
    (copied : ∀ i < bs.length, s.mem (State.addr (dst + BitVec.ofNat 32 i)) = bs[i]?.getD 0)
    (mask : s.gpr .r7 = BitVec.ofNat 32 (2 ^ (j + 1) - 1)) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeFirst) s fun t =>
      ShapeContext dst src bs bits t ∧ t.gpr .r4 = dst ∧
      (∀ i < bs.length, t.mem (State.addr (dst + BitVec.ofNat 32 i)) =
        (VG.Proof.Ffdh.ParameterCandidate.topCut bs j).getD i 0) ∧
      Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem ∧ Rest [.r3, .r4, .r9] s t := by
  have positive : 0 < bs.length := by have := h.size; omega
  have read := h.readByte (i := 0) positive
  have write := h.writeByte (i := 0) positive
  simp only [BitVec.add_zero] at read write
  refine WP.mono (shapeFirst_ok s dst bound (h.frame.read (d := 4) (by decide))
    (h.frame.saved 4 (by decide)) read write mask) ?_
  rintro t ⟨⟨ptr, mem⟩, rest⟩
  have contains := h.containsByte (i := 0) positive
  simp only [BitVec.add_zero] at contains
  have frame : Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (by simp) _ contains
  refine ⟨h.after_output frame rest, ptr, ?_, frame, rest⟩
  intro i hi
  rw [mem, VG.WriteBytes.writeW8_apply, VG.Proof.Ffdh.ParameterCandidate.topCut_getD]
  by_cases first : i = 0
  · subst i
    simp only [BitVec.add_zero, ite_true]
    have byte := copied 0 positive
    simp only [BitVec.add_zero] at byte
    rw [byte]
    rfl
  · have different : State.addr (dst + BitVec.ofNat 32 i) ≠ State.addr dst := by
      intro same
      have eq := h.copyCtx.distinct i hi 0 positive (by simpa using same)
      exact first eq
    rw [ite_eq_right different, ite_eq_right first]
    exact copied i hi

end VG.Proof.Ffdh.Arm.ParameterCandidate
