import VerifiedGarbage.Impl.Ed448.Arm.VerifyEquation
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 verification's equation on ARMv7: the contract the proof is written against

The facts of `Spec.Ed448.verifyEquationContract` the proof uses, stated for
ARMv7, in a module of their own: callers proven for any code meeting them
need not import the proof.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm

/-- `vg_ed448_verify_equation(pk = r0, signature = r1, challenge = r2, scratch = r3) -> r0`. -/
def verifyEquationLocal : Contract Arm.isa where
  pre s :=
    let pk : Region := ⟨State.addr (s.gpr .r0), 57⟩
    let sig : Region := ⟨State.addr (s.gpr .r1), 114⟩
    let ch : Region := ⟨State.addr (s.gpr .r2), 57⟩
    let ws : Region := ⟨State.addr (s.gpr .r3), 8192⟩
    s.rd = [pk, sig, ch] ∧ s.wr = [ws] ∧ pk.Disjoint ws ∧ sig.Disjoint ws ∧ ch.Disjoint ws ∧
      (s.gpr .r0).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 114 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32
  post s t := t.gpr .r0 = if Spec.Ed448.verifyEquation
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r0)) 57)
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 114)
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r2)) 57) then 1 else 0
  pub s t := s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧
    s.gpr .r3 = t.gpr .r3 ∧ s.sp = t.sp

end VG.Proof.Ed448.Arm
