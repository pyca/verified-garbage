module

public import VerifiedGarbage.Proof.Ed448.AArch64.ScalarMulAddMain
import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Ed448.AArch64.ScalarMain
import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed448.AArch64.ScalarMulAddMain
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Ed448.AArch64.ScalarMain
meta import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 scalar arithmetic on AArch64: `Verified`

Correctness includes the ABI. Taint analysis checks that secret input bytes
never determine branches or memory addresses: only the arguments, which
are public, do. A concrete witness proves the signature contract is
satisfiable.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64

theorem scalarReduce_ok (s : State) (hs : scalarReduceLocal.pre s) :
    ∃ t s', Exec isa scalarReduce s t s' ∧ abiPreserved s s' ∧ scalarReduceLocal.post s s' :=
  scalarReduce_correct hs

theorem scalarReduce_ct :
    ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨hsp, h0, h1, h2⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h0, h1, h2]

theorem scalarMulAdd_ok (s : State) (hs : scalarMulAddLocal.pre s) :
    ∃ t s', Exec isa scalarMulAdd s t s' ∧ abiPreserved s s' ∧ scalarMulAddLocal.post s s' :=
  scalarMulAdd_correct hs

theorem scalarMulAdd_ct :
    ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨hsp, h0, h1, h2, h3, h4⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4]

end VG.Proof.Ed448.AArch64
