module
public import VerifiedGarbage.Proof.X25519.Arm.Instr


/-! # Branch on the proved public-exponent validity bit -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest wp_subs op2_imm)

theorem exponentFlag_ok (s : State) {valid : Bool} (status : s.gpr .r7 = BitVec.ofNat 32 valid.toNat) :
    WP isa (.block [.subs .r7 .r7 (.imm 0)]) s fun t => t.z = !valid ∧ t.mem = s.mem ∧ Rest [.r7] s t := by
  refine wp_subs (op2_imm (by decide)) fun t a zero => WP.block_nil ?_
  refine ⟨?_, a.mem, a.rest (by simp)⟩
  cases valid <;> simpa [status] using zero

end VG.Proof.Bignum.Arm
