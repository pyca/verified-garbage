module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.X86.Target

/-! # The shared candidate contract exposes native cdecl arguments and a static sieve table -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

def contract : Contract isa := Spec.RsaKeyGen.candidateContract
  (abi.withConsts VG.Impl.RsaKeyGen.TrialTable32.consts) 152

def callEnvironment (s : State) : Environment where
  workspace := arg s 9
  capacity := (arg s 10).toNat
  out := arg s 0
  used := arg s 2
  exponent := arg s 3
  other := arg s 5
  rand := arg s 7
  table := s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol
  length := (arg s 1).toNat
  exponentLength := (arg s 4).toNat
  otherLength := (arg s 6).toNat
  randLength := (arg s 8).toNat
  p := s.gpr .esp - 16#32

theorem packed_length : VG.Impl.RsaKeyGen.TrialTable32.packed.length = 1024 := by
  simp only [VG.Impl.RsaKeyGen.TrialTable32.packed, List.length_map, List.length_range]

structure CallSizes (s : State) : Prop where
  length : Spec.RsaKeyGen.primeLenValid (arg s 1).toNat
  exponentLength : 1 ≤ (arg s 4).toNat ∧ (arg s 4).toNat ≤ 8
  otherLength : (arg s 6).toNat = 0 ∨ (arg s 6).toNat = (arg s 1).toNat
  capacity : Spec.Rsa.scratchWords (arg s 1).toNat ≤ (arg s 10).toNat

theorem call_sizes {s : State} (h : contract.pre s) : CallSizes s := by
  sig_pre [contract, Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts,
    packed_length, stackBelow] at h
  sig_split h
  constructor <;> first
    | with_reducible assumption
    | (constructor <;> with_reducible assumption)

structure CallLayout (s : State) : Prop where
  low : 152 ≤ (s.gpr .esp).toNat
  argsFit : (s.gpr .esp).toNat + 48 ≤ 2 ^ 32
  outFit : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  usedFit : (arg s 2).toNat + 8 ≤ 2 ^ 32
  exponentFit : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  otherFit : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  randFit : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  workspaceFit : (arg s 9).toNat + 8 * (arg s 10).toNat ≤ 2 ^ 32
  wr : s.wr = [(callEnvironment s).outRegion, (callEnvironment s).usedRegion,
    (callEnvironment s).workspaceRegion, ⟨argAddr s 0, 44⟩]
  rdPrefix : s.rd.take (s.rd.length - 1) =
    [(callEnvironment s).exponentRegion, (callEnvironment s).otherRegion, (callEnvironment s).randRegion]
  rdTable : s.rd.drop (s.rd.length - 1) = Abi.constRegions (fun n => (s.syms n).setWidth 64)
    VG.Impl.RsaKeyGen.TrialTable32.consts

theorem call_layout {s : State} (h : contract.pre s) : CallLayout s := by
  sig_pre [contract, Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts,
    packed_length, stackBelow] at h
  sig_split h
  constructor <;> try with_reducible assumption
  all_goals try dsimp only [callEnvironment, Environment.outRegion, Environment.usedRegion,
    Environment.workspaceRegion, Environment.exponentRegion, Environment.otherRegion, Environment.randRegion,
    Environment.base, Environment.size, VG.Impl.RsaKeyGen.TrialTable32.consts]
  all_goals simp only [Nat.mul_comm] at *
  all_goals assumption

end VG.Proof.RsaKeyGen.X86.Candidate
