module

public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABI
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.TimingBody
public import VerifiedGarbage.Spec.MillerRabin
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABIEntry
import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
import VerifiedGarbage.Proof.Framework.Sig

/-! # The test is constant time under the shared contract's leak -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86

structure PublicInputs (bits : Nat) (s t : State) : Prop where
  stack : s.gpr .esp = t.gpr .esp
  symbol : s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol
  observations : Spec.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem
      ((arg s 0).setWidth 64) :: (callEntropy s).map (·.toNat) =
    Spec.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) t.mem
      ((arg t 0).setWidth 64) :: (callEntropy t).map (·.toNat)
  arg0 : arg s 0 = arg t 0
  arg1 : arg s 1 = arg t 1
  arg2 : arg s 2 = arg t 2
  arg3 : arg s 3 = arg t 3
  arg4 : arg s 4 = arg t 4

theorem public_inputs {bits : Nat} {s t : State} (H : (contract bits).pub s t) : PublicInputs bits s t := by
  sig_pub [contract, Spec.Dsa.ProbablePrime.contract, Spec.Dsa.ProbablePrime.sig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at H
  sig_split H
  constructor <;> first | with_reducible assumption | (dsimp only [callEntropy]; with_reducible assumption)

theorem PublicInputs.environment {bits : Nat} {s t : State} (P : PublicInputs bits s t) :
    callEnvironment bits s = callEnvironment bits t := by
  simp only [callEnvironment, P.arg0, P.arg1, P.arg2, P.arg3, P.arg4, P.stack, P.symbol]

theorem PublicInputs.candidate {bits : Nat} {s t : State} (P : PublicInputs bits s t) :
    (callEnvironment bits s).candidate s.mem = (callEnvironment bits t).candidate t.mem :=
  (List.cons.inj P.observations).1

theorem PublicInputs.entropy {bits : Nat} {s t : State} (P : PublicInputs bits s t) :
    callEntropy s = callEntropy t :=
  VG.Proof.RsaKeyGen.map_toNat_inj (List.cons.inj P.observations).2

theorem constantTime {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56) {bits : Nat} (b : Bits bits) :
    ConstantTime isa (contract bits).pre (contract bits).pub
      (VG.Impl.Dsa.X86.ProbablePrime.code bits montName mont roundName round) := by
  apply RelCT.constantTime
  intro s t tr ur u z ⟨HS, HT, HP⟩ A B
  have P := public_inputs HP
  have F := call_facts HS
  have G := call_facts HT
  have I := F.entry b
  have J := G.entry b
  rw [← P.candidate, ← P.environment, ← P.entropy] at J
  exact framed_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack (F.valid b)
    F.odd F.length _ _ _ _ _ _ ⟨⟨I, J⟩, P.stack⟩ A B

end VG.Proof.Dsa.X86.ProbablePrime
