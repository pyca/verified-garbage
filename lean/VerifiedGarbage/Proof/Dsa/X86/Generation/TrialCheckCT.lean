module
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialCTState
public import VerifiedGarbage.Proof.Dsa.X86.RandomContext
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.AllocationCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialBodyCT

/-! # The trial helper's stack frame does not add secret-dependent leakage -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

def TrialCallAt (len entries : Nat) (p : TrialPublic) (s : State) : Prop :=
  16 ≤ (s.gpr .esp).toNat ∧ TrialInputs (allocated 16 s) p.base p.input p.table len entries ∧
    trialValue s p.input len = p.value ∧ s.gpr .esi = p.input ∧ s.gpr .edi = p.table

theorem trialCheck_ct (len entries : Nat) :
    RelCT isa (Two (TrialCallAt len entries)) (trialCheck len entries) (fun _ _ => True) := by
  apply allocation_ct (by decide) (fun _ _ h => h.1) (ct := trialCheckBody_ct len entries)
  intro p s R
  exact ⟨R.2.1, R.2.2.1, (allocated_gpr _ _ (by decide)).trans R.2.2.2.1,
    (allocated_gpr _ _ (by decide)).trans R.2.2.2.2⟩
end VG.Proof.Dsa.X86.Generation
