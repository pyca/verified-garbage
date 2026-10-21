module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABIMemory
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSchedule
import VerifiedGarbage.Proof.Bignum.Octets

/-! # The shared contract publishes arguments, table address, exponent bytes, and only its declared candidate leak -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.RsaKeyGen

structure PublicInputs (s t : State) : Prop where
  stack : s.gpr .esp = t.gpr .esp
  arguments : ∀ i < 11, arg s i = arg t i
  tables : s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol
  observations : (callEBytes s).map (·.toNat) ++
      Spec.RsaKeyGen.candidateLeak (arg s 1).toNat (callEBytes s) (callPBytes s) (callEntropy s) =
    (callEBytes t).map (·.toNat) ++
      Spec.RsaKeyGen.candidateLeak (arg t 1).toNat (callEBytes t) (callPBytes t) (callEntropy t)

theorem public_inputs {s t : State} (H : contract.pub s t) : PublicInputs s t := by
  sig_pub [contract, Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at H
  sig_split H
  refine ⟨by with_reducible assumption, ?_, by with_reducible assumption, by dsimp only [callEBytes, callPBytes, callEntropy]; with_reducible assumption⟩
  intro i index
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem PublicInputs.table {s t : State} (P : PublicInputs s t) :
    s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol := by
  exact P.tables

theorem PublicInputs.environment {s t : State} (P : PublicInputs s t) : callEnvironment s = callEnvironment t := by
  simp only [callEnvironment, P.arguments 0 (by decide), P.arguments 1 (by decide), P.arguments 2 (by decide),
    P.arguments 3 (by decide), P.arguments 4 (by decide), P.arguments 5 (by decide), P.arguments 6 (by decide),
    P.arguments 7 (by decide), P.arguments 8 (by decide), P.arguments 9 (by decide), P.arguments 10 (by decide),
    P.stack, P.table]

theorem PublicInputs.exponent {s t : State} (P : PublicInputs s t) : callEBytes s = callEBytes t := by
  have lengths : ((callEBytes s).map (·.toNat)).length = ((callEBytes t).map (·.toNat)).length := by
    simp only [List.length_map, callEBytes, VG.Proof.Bignum.bytesAt_length, P.arguments 4 (by decide)]
  exact map_toNat_inj (List.append_inj P.observations lengths).1

theorem PublicInputs.leak {s t : State} (P : PublicInputs s t) :
    SameLeak (callEnvironment s) (callEBytes s) (callPBytes s) (callPBytes t) (callEntropy s) (callEntropy t) := by
  have lengths : ((callEBytes s).map (·.toNat)).length = ((callEBytes t).map (·.toNat)).length := by
    simp only [List.length_map, callEBytes, VG.Proof.Bignum.bytesAt_length, P.arguments 4 (by decide)]
  have L := (List.append_inj P.observations lengths).2
  rw [← P.arguments 1 (by decide), ← P.exponent] at L
  exact L

end VG.Proof.RsaKeyGen.X86.Candidate
