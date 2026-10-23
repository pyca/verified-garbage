module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Static
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Framework.Contract

/-! Untrusted local contract for the sparse verification equation. Timing may
reveal the public signature and challenge scalars, as permitted by the shared
reviewed verification contract. Point coordinates are never public for timing. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Sparse




def signatureScalar (s:State) : Nat:=
  Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .x1+BitVec.ofNat 64 57) 57)
def challengeScalar (s:State) : Nat:=
  Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57)

/-- `vg_ed448_verify_equation(pk = x0, signature = x1, challenge = x2, scratch = x3) -> w0`,
with the odd affine base table at the static `baseSym`. -/
def verifyEquationLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x1, 114⟩, ⟨s.gpr .x2, 57⟩,
      ⟨s.syms baseSym, 8 * baseWords.length⟩] ∧
    s.wr = [⟨s.gpr .x3, 8192⟩] ∧
    (⟨s.gpr .x0, 57⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (⟨s.gpr .x1, 114⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (⟨s.gpr .x2, 57⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64 ∧ BaseHeld s [⟨s.gpr .x3, 8192⟩]
  post s t := t.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .x0) 57)
    (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57) then 1 else 0
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧ s.syms baseSym = t.syms baseSym ∧
    signatureScalar s=signatureScalar t ∧ challengeScalar s=challengeScalar t

theorem verifyEquation_noFrames : verifyEquation.noFrames = true := by decide +kernel

/-- `vg_ed448_verify_equation` meets `verifyEquationLocal` and the ABI, in constant time. -/
structure EqOk : Prop where
  ok : ∀ s, verifyEquationLocal.pre s →
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s'
  ct : ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub verifyEquation

end VG.Proof.Ed448.AArch64.Sparse
