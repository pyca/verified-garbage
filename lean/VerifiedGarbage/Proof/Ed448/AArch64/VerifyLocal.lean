import VerifiedGarbage.Proof.Ed448.AArch64.VerifyErase
import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 verification's equation on AArch64: the contract its callers use

Untrusted: everything here is checked by Lean. The contract the proof is
written against (the facts of `Spec.Ed448.verifyEquationContract` it uses,
stated for AArch64), that the function has no frames, and `EqOk`: that it
meets the contract in constant time. `VerifyVerified.lean` proves `EqOk` with
the group law and the field arithmetic; the proofs of the functions that call
`vg_ed448_verify_equation` take it as a hypothesis, which their registration
files pass in, so that they do not import that algebra.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64

/-- `vg_ed448_verify_equation(pk = x0, signature = x1, challenge = x2, scratch = x3) -> w0`. -/
def verifyEquationLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x1, 114⟩, ⟨s.gpr .x2, 57⟩] ∧
    s.wr = [⟨s.gpr .x3, 8192⟩] ∧
    (⟨s.gpr .x0, 57⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (⟨s.gpr .x1, 114⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (⟨s.gpr .x2, 57⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64
  post s t := t.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .x0) 57)
    (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57) then 1 else 0
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3

theorem verifyEquation_noFrames : verifyEquation.noFrames = true := by
  rw [← Code.noFrames_eraseImm, verifyEquation_eraseImm]; decide +kernel

/-- `vg_ed448_verify_equation` meets `verifyEquationLocal` and the ABI, in constant time. -/
structure EqOk : Prop where
  ok : ∀ s, verifyEquationLocal.pre s →
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s'
  ct : ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub verifyEquation

end VG.Proof.Ed448.AArch64
