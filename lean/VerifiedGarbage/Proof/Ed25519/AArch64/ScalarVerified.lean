module

public import VerifiedGarbage.Proof.Ed25519.Contract
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

/-! Scalar reduction satisfies the merged specification, ABI, and constant-time contract. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def scalarSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩]

theorem scalarReduce_ok (s : State) (hs : scalarReduceLocal.pre s) :
    ∃ t s', Exec isa scalarReduce s t s' ∧ abiPreserved s s' ∧ scalarReduceLocal.post s s' :=
  scalarReduce_correct hs

theorem scalarReduce_ct : ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨hsp, h0, h1, h2⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> assumption

theorem scalarReduce_verified : Verified AArch64.target scalarReduce
    (Proof.Ed25519.scalarReduceContract AArch64.abi) :=
  Verified.of_correct scalarReduce_ok scalarReduce_ct (by
    sig_implies [Proof.Ed25519.scalarReduceContract, Proof.Ed25519.scalarReduceSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, scalarReduceLocal]
      [scalarSatState] using scalarSatState)

end VG.Proof.Ed25519.AArch64
