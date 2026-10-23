module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI

/-! # The candidate signature separates every writable buffer from live inputs and the call frame -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

def inputRegions (E : Environment) : List Region := [E.exponentRegion, E.otherRegion, E.randRegion]
def reservedRegion (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 152#64, 152⟩

structure CallSeparation (s : State) : Prop where
  outUsed : (callEnvironment s).outRegion.Disjoint (callEnvironment s).usedRegion
  outWorkspace : (callEnvironment s).outRegion.Disjoint (callEnvironment s).workspaceRegion
  usedWorkspace : (callEnvironment s).usedRegion.Disjoint (callEnvironment s).workspaceRegion
  argsWorkspace : (⟨argAddr s 0, 44⟩ : Region).Disjoint (callEnvironment s).workspaceRegion
  readWrite : ∀ r ∈ inputRegions (callEnvironment s), ∀ R ∈ (callEnvironment s).writeRegions, r.Disjoint R
  stackFar : ∀ r ∈ (callEnvironment s).writeRegions ++ inputRegions (callEnvironment s), r.Disjoint (reservedRegion s)
  returnFar : ∀ r ∈ (callEnvironment s).writeRegions, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r
  tableHeld : Abi.constsHeld s.mem (fun name => (s.syms name).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts
  tableFar : ∀ t ∈ Abi.constRegions (fun name => (s.syms name).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts,
    t.base.toNat + t.len ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
    t.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ∧ t.Disjoint (reservedRegion s)

theorem call_separation {s : State} (h : contract.pre s) : CallSeparation s := by
  sig_pre [contract, Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts,
    packed_length, stackBelow] at h
  sig_split h
  constructor <;> try with_reducible assumption
  all_goals dsimp only [callEnvironment, inputRegions, reservedRegion, Environment.outRegion,
    Environment.usedRegion, Environment.workspaceRegion, Environment.exponentRegion, Environment.otherRegion,
    Environment.randRegion, Environment.base, Environment.size, Environment.writeRegions,
    VG.Impl.RsaKeyGen.TrialTable32.consts]
  all_goals try simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc, forall_eq_or_imp, forall_eq]
  all_goals repeat' apply And.intro
  all_goals simp only [Nat.mul_comm] at *
  all_goals first | with_reducible assumption | exact Region.Disjoint.symm (by with_reducible assumption)

end VG.Proof.RsaKeyGen.X86.Candidate
