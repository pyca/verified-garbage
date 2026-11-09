module

public import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMain
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMain
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Spec.Ed25519.Contract

/-! Scalar reduction satisfies the merged specification, ABI, and constant-time contract. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem scalarReduce_ok (s : State) (hs : scalarReduceLocal.pre s) :
    ∃ t s', Exec isa scalarReduce s t s' ∧ abiPreserved s s' ∧ scalarReduceLocal.post s s' :=
  scalarReduce_correct hs

theorem scalarReduce_ct : ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨hsp, h0, h1, h2⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> assumption

end VG.Proof.Ed25519.AArch64
