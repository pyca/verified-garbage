module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSizes
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEncodedResult
import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Tactic.IntervalCases

/-! # The shared key contract publishes its arguments, exponent bytes and result status -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

def callEBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (callEnvironment s).exponentRegion.base (callEnvironment s).exponentRegion.len
def callKeyStatus (s : State) : Nat := Spec.RsaKeyGen.keyStatus (encodedOperation (callEnvironment s) s.mem)

structure PublicInputs (s t : State) : Prop where
  stack : s.gpr .esp = t.gpr .esp
  arguments : ∀ i < 18, arg s i = arg t i
  observations : (callEBytes s).map (·.toNat) ++ [callKeyStatus s] =
    (callEBytes t).map (·.toNat) ++ [callKeyStatus t]

theorem public_inputs {s t : State} (H : contract.pub s t) : PublicInputs s t := by
  sig_pub [contract, keyStack, Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig,
    abi, argSlots, argVal, argBytes] at H
  sig_split H
  refine ⟨by with_reducible assumption, ?_, ?_⟩
  · intro i hi
    interval_cases i <;> with_reducible assumption
  · dsimp only [callEBytes, callKeyStatus, encodedOperation, callEnvironment,
      Environment.exponentRegion, Environment.outputRegion, Environment.outputLength]
    simp only [Nat.reduceMul, Nat.reduceLT, ite_true, ite_false]
    with_reducible assumption

theorem PublicInputs.environment {s t : State} (P : PublicInputs s t) : callEnvironment s = callEnvironment t := by
  simp only [callEnvironment, P.arguments 16 (by decide), P.arguments 17 (by decide),
    P.arguments 5 (by decide), P.arguments 14 (by decide), P.arguments 15 (by decide)]
  congr 1
  funext i
  by_cases hi : i < 7
  · simp only [hi, ite_true]
    exact P.arguments (2 * i) (by omega)
  · simp only [hi, ite_false]

theorem PublicInputs.exponent {s t : State} (P : PublicInputs s t) : callEBytes s = callEBytes t := by
  have lengths : ((callEBytes s).map (·.toNat)).length = ((callEBytes t).map (·.toNat)).length := by
    simp only [List.length_map, callEBytes, VG.Proof.Bignum.bytesAt_length, P.environment]
  exact VG.Proof.RsaKeyGen.map_toNat_inj (List.append_inj P.observations lengths).1

theorem PublicInputs.status {s t : State} (P : PublicInputs s t) : callKeyStatus s = callKeyStatus t := by
  have lengths : ((callEBytes s).map (·.toNat)).length = ((callEBytes t).map (·.toNat)).length := by
    rw [P.exponent]
  exact List.singleton_inj.mp (List.append_inj P.observations lengths).2

end VG.Proof.RsaKeyGen.X86.Key
