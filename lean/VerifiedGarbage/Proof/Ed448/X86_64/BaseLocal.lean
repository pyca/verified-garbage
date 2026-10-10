import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig

/-!
# Ed448 base-point multiplication on x86-64: the contract the proof is written against

The facts of `Spec.Ed448.scalarBaseContract` the proof uses, stated for
x86-64, in a module of their own: callers proven for any code meeting them
need not import the proof, and the group theory it imports.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64

/-- `vg_ed448_scalar_base(out = rdi, scalar = rsi, scratch = rdx)`. -/
def scalarBaseLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rsi, 57⟩] ∧ s.wr = [⟨s.gpr .rdi, 57⟩, ⟨s.gpr .rdx, 8192⟩] ∧
    (⟨s.gpr .rsi, 57⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 57⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (⟨s.gpr .rdi, 57⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64
  post s t := Spec.Ed448.bytesAt t.mem (s.gpr .rdi) 57 =
    Spec.Ed448.scalarBase (Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 57)
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧
    s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx

/-- The 8 bytes below `rsp = B + 8`, where a call from it stores its return address. -/
theorem hole_add8 (B : Addr) : hole (B + BitVec.ofNat 64 8) = ⟨B, 8⟩ := by
  simp only [hole]
  rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, BitVec.add_sub_cancel]

end VG.Proof.Ed448.X86_64
