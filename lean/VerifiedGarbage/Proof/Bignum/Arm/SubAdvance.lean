module

public import VerifiedGarbage.Impl.Bignum.Arm.SubRow
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance

/-! # Public pointer and counter updates of a subtraction row -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_dp op2_imm dpVal)

theorem subAdvance_ok (s : State) :
    WP isa (.block subAdvance) s fun t =>
      t.gpr .r0 = s.gpr .r0 + 4 ∧ t.gpr .r10 = s.gpr .r10 + 4 ∧
      t.gpr .r12 = s.gpr .r12 + 4 ∧ t.gpr .lr = s.gpr .lr - 1 ∧
      t.z = (s.gpr .lr - 1 == 0) ∧ t.mem = s.mem ∧ Rest [.r0, .r10, .r12, .lr] s t := by
  unfold subAdvance
  refine wp_dp (op2_imm (by decide)) fun u hu => ?_
  refine WP.mono (rowAdvance_ok u) ?_
  rintro t ⟨p0, p12, cnt, zero, mem, keep⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p0, hu.other .r0 (by decide)]
  · rw [keep.gpr .r10 (by simp), hu.gpr, dpVal]
  · rw [p12, hu.other .r12 (by decide)]
  · rw [cnt, hu.other .lr (by decide)]
  · rw [zero, hu.other .lr (by decide)]
  · rw [mem, hu.mem]
  · exact (hu.rest (by simp)).trans (keep.mono (by simp_all))

end VG.Proof.Bignum.Arm
