import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 verification's equation on AArch64: the contract the proof is written against

The facts of `Spec.Ed448.verifyEquationContract` the proof uses, stated for
AArch64, in a module of their own: callers proven for any code meeting them
need not import the proof, and the group theory it imports.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64

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

end VG.Proof.Ed448.AArch64
