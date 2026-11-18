module

import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Correct
public import VerifiedGarbage.Spec.TripleDes.Contract
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.AArch64.Lit
public import VerifiedGarbage.Proof.TripleDes.AArch64.ConstantTime
import VerifiedGarbage.Proof.Framework.AArch64.Clears

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 384⟩]

theorem correct (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa Impl.TripleDes.AArch64.Key.expandKey s t s' ∧ abiPreserved s s' ∧ contract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := expand_correct s hs
  exact ⟨t, s', he, ⟨ha, VG.AArch64.Exec.sp he, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem publicRegs_three (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 := by
  simp [PublicRegs]

theorem verified : Verified target Impl.TripleDes.AArch64.Key.expandKey
    (Spec.TripleDes.expandKeyContract abi) := by
  refine Verified.of_correct correct (expandKey_constantTime _) ?_
  sig_implies [Spec.TripleDes.expandKeyContract, Spec.TripleDes.expandKeySig,
    Spec.TripleDes.expandKeyPre, Spec.TripleDes.expandKeyPost, abi, argRegs,
    contract, publicRegs_three] [satState] using satState

/-- The key expansion, with what it leaves cleared, meets the same contract. -/
theorem verifiedCleared : Verified target Proof.TripleDes.AArch64.expandKeyCleared
    (Spec.TripleDes.expandKeyContract abi) :=
  Clears.Verified.withClears verified (by decide)

end VG.Proof.TripleDes.AArch64.Key
