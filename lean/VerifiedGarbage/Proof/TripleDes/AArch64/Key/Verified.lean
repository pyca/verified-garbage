module

import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Correct
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.TripleDes.Scratch
public import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Contract
public import VerifiedGarbage.Proof.TripleDes.AArch64.Lit
public import VerifiedGarbage.TCB.AArch64.Target
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Permutation
import VerifiedGarbage.Proof.TripleDes.AArch64.Permutation
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Spec.Rc2

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 384⟩, ⟨0x3000, 512⟩]

theorem correct (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa Impl.TripleDes.AArch64.Key.expandKey s t s' ∧ abiPreserved s s' ∧ contract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := expand_correct s hs
  exact ⟨t, s', he, ⟨ha, VG.AArch64.Exec.sp he, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2, .x3] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 := by simp [PublicRegs]

theorem verified : Verified target Impl.TripleDes.AArch64.Key.expandKey
    (Proof.TripleDes.expandKeyScratchContract abi) := by
  refine Verified.of_correct correct (expandKey_constantTime _) ?_
  sig_implies [Proof.TripleDes.expandKeyScratchContract, Proof.TripleDes.expandKeyScratchSig, Spec.TripleDes.expandKeyPre, Spec.TripleDes.expandKeyPost, abi, argRegs,
    contract, publicRegs_four] [satState] using satState

end VG.Proof.TripleDes.AArch64.Key
