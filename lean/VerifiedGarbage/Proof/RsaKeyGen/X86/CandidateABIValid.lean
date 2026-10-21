module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABIRegions
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABIGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABITable

/-! # Every state admitted by the shared candidate contract satisfies its native geometry -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

theorem call_valid {s : State} (h : contract.pre s) : (callEnvironment s).Valid := by
  have A := call_layout h
  have Z := call_sizes h
  have D := call_separation h
  refine ⟨Z.length, Z.exponentLength, Z.otherLength, Z.capacity,
    A.workspaceFit, A.outFit, A.usedFit, A.exponentFit, A.otherFit, A.randFit, (arg s 8).isLt,
    ?_, ?_, ?_, A.workspaceStack Z D, ?_, ?_, D.outUsed, D.outWorkspace, D.usedWorkspace,
    D.readWriteAll A, ?_⟩
  · have fit := D.tableProperties.1
    change ((s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64).toNat + 8192 ≤ 2 ^ 32 at fit
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (s.syms _).isLt (by decide))] at fit
    exact fit
  · rw [A.privateNat]
    have := A.low
    omega
  · rw [A.privateNat]
    have := A.low
    have := A.argsFit
    omega
  · intro r mem
    exact (D.stackAll A r mem).sub_right A.savedSub
  · rw [call_args_address]
    exact D.argsWorkspace
  · intro r mem
    exact (D.stackAll A r mem).sub_right A.bodyStackSub

end VG.Proof.RsaKeyGen.X86.Candidate
