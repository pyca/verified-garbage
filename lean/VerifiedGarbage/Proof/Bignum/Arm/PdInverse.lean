module

public import VerifiedGarbage.Proof.Bignum.Arm.PdBodyInput
public import VerifiedGarbage.Proof.Bignum.Arm.PdArithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.PdCheckRest
import VerifiedGarbage.Proof.Bignum.Arm.PdChecks
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse

/-! # Establish arithmetic readiness without recomputing the packed R² -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem pdInverse_ok (s : State) {base dst pp ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb : List Byte}
    (h : PdBodyInput base dst pp ep xp len k eLen N R eb xb s)
    (check : PdCheckState base len (Spec.Rsa.modulusWords k) N R s)
    (accepted : pdAccepted N R = true) :
    WP isa precomputeInverse s fun t => PdArithmetic base dst pp ep xp len k eLen N R eb xb t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  obtain ⟨large, bound, odd⟩ := pdAccepted_facts accepted
  refine WP.mono (precomputeInverse_r2_ok s check.ready.workspace check.ready.layout check.ready.width
    check.ready.ptr (by rw [check.modulus]; exact odd) (by rw [check.modulus]; exact large)
    check.ready.stackRead check.ready.stackSep check.ready.saved) ?_
  rintro t ⟨ready, modulus, frame, rest, r2⟩
  exact ⟨⟨h.buffers.after_workspace frame rest, h.stack.after_workspace frame rest, ready,
    modulus.trans check.modulus, odd, r2.trans check.r2, bound⟩, frame, rest⟩
end VG.Proof.Bignum.Arm
