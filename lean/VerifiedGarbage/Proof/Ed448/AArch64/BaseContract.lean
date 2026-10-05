import VerifiedGarbage.Proof.Ed448.AArch64.Base.Erase
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.TCB.AArch64.Target

/-!
# Ed448 base-point multiplication on AArch64: the contract its callers use

Untrusted: everything here is checked by Lean. The contract the proof is
written against (the facts of `Spec.Ed448.scalarBaseContract` it uses, stated
for AArch64), that the function has no frames, and `BaseOk`: that it meets
the contract in constant time. `BaseVerified.lean` proves `BaseOk` with the
group law and the comb's arithmetic; the proofs of the functions that call
`vg_ed448_scalar_base` take it as a hypothesis, which their registration files
pass in, so that they do not import that algebra.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Spec.Ed448 (bytesAt)

/-- `vg_ed448_scalar_base(out = x0, scalar = x1, scratch = x2)`. -/
def scalarBaseLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 57⟩] ∧ s.wr = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x2, 8192⟩] ∧
    (⟨s.gpr .x0, 57⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
    (⟨s.gpr .x1, 57⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
    (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64
  post s t := bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarBase (bytesAt s.mem (s.gpr .x1) 57)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2

theorem scalarBase_noFrames : scalarBase.noFrames = true := by
  rw [← Code.noFrames_eraseImm, scalarBase_eraseImm]; decide +kernel

/-- `vg_ed448_scalar_base` meets `scalarBaseLocal` and the ABI, in constant time. -/
structure BaseOk : Prop where
  ok : ∀ s, scalarBaseLocal.pre s →
    ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s'
  ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase

end VG.Proof.Ed448.AArch64
