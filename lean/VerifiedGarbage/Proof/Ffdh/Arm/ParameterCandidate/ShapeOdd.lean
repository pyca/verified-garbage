module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeContext
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeLast
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Omega

/-! Setting the final bit preserves the full shaped encoding and its frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

theorem shapeOdd_ok (s : State) {dst src : BitVec 32} {bs xs : List Byte} {bits : Nat}
    (h : ShapeContext dst src bs bits s) (length : xs.length = bs.length)
    (copied : ∀ i < bs.length, s.mem (State.addr (dst + BitVec.ofNat 32 i)) = xs[i]?.getD 0)
    (dest : s.gpr .r4 = dst) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeLast) s fun t =>
      ShapeContext dst src bs bits t ∧
      (∀ i < bs.length, t.mem (State.addr (dst + BitVec.ofNat 32 i)) =
        (VG.Proof.Ffdh.ParameterCandidate.lastOne xs).getD i 0) ∧
      Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem ∧ Rest [.r3, .r4, .r5] s t := by
  have size := h.size
  have last : bs.length - 1 < bs.length := by omega
  have ptr : s.gpr .r4 + BitVec.ofNat 32 bs.length - 1 =
      dst + BitVec.ofNat 32 (bs.length - 1) := by
    rw [dest, BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg]
    change dst + (BitVec.ofNat 32 bs.length - BitVec.ofNat 32 1) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  refine WP.mono (shapeLast_ok s bs.length (h.frame.read (d := 12) (by decide))
    (h.frame.saved 12 (by decide)) (by rw [ptr]; exact h.readByte last)
    (by rw [ptr]; exact h.writeByte last)) ?_
  rintro t ⟨⟨_, mem⟩, rest⟩
  rw [ptr, copied _ last] at mem
  have frame : Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (by simp) _ (h.containsByte last)
  refine ⟨h.after_output frame rest, ?_, frame, rest⟩
  intro i hi
  have hi' : i < xs.length := by omega
  rw [VG.Proof.Ffdh.ParameterCandidate.lastOne_getD hi', length, mem, VG.WriteBytes.writeW8_apply]
  by_cases final : i + 1 = bs.length
  · have same : i = bs.length - 1 := by omega
    subst i
    rw [ite_eq_left rfl, ite_eq_left final]
    rfl
  · have different : State.addr (dst + BitVec.ofNat 32 i) ≠
        State.addr (dst + BitVec.ofNat 32 (bs.length - 1)) := by
      intro same
      have := h.copyCtx.distinct i hi (bs.length - 1) last same
      omega
    rw [ite_eq_right different, ite_eq_right final]
    exact copied i hi

end VG.Proof.Ffdh.Arm.ParameterCandidate
