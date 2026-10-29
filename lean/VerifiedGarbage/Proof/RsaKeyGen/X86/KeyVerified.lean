module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyABI
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySatisfiable
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFrameResult
import Init.Data.BitVec.Basic
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPublicLeak
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFrameTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallArgs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallValid
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSamples
/-! # Complete native RSA key generation has correctness, timing and satisfiability certificates -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyCorrect.lean`, which only this module imported.
section

/-! # Complete native key generation satisfies the shared encoded cdecl contract -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

theorem correct (s : State) (h : contract.pre s) :
    ∃ trace t, Exec isa VG.Impl.RsaKeyGen.X86.Key.code s trace t ∧
      abiPreserved s t ∧ contract.post s t := by
  have Z := call_sizes h
  obtain ⟨trace, t, run, preserved, R⟩ := framed_result_ok h
  refine ⟨trace, t, run, preserved, ?_⟩
  sig_post [contract, keyStack, Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig,
    abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  unfold EncodedResult encodedOperation at R
  simp only [callEnvironment, Environment.exponentRegion, Environment.outputRegion, Environment.outputLength,
    List.range_succ, List.range_zero, List.map_nil, List.map_cons, List.nil_append, List.cons_append,
    Nat.reduceMul, Nat.reduceLT, ite_true, ite_false] at R
  rw [← Z.modulus] at R
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at R
  generalize result : Spec.RsaKeyGen.keyOp (arg s 5).toNat
    (Spec.Rsa.bytesAt s.mem ((arg s 14).setWidth 64) (arg s 15).toNat)
    (Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat)
    (Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64) (arg s 5).toNat) = value at R ⊢
  cases value with
  | inl answer => cases answer <;> exact R
  | inr u => cases u; exact R

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyConstantTime.lean`, which only this module imported.
section

/-! # Native key assembly is constant time under exactly the shared API's declared observations -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

theorem constantTime : ConstantTime isa contract.pre contract.pub VG.Impl.RsaKeyGen.X86.Key.code := by
  apply RelCT.constantTime
  intro s t tr ur u z ⟨HS, HT, HP⟩ A B
  have P := public_inputs HP
  have I := entry_input HS
  have J := entry_input HT
  have stack : callSp s = callSp t := by unfold callSp; rw [P.stack]
  rw [← P.environment, ← stack] at J
  have rightExponent := entered_exponent HT
  have rightP := entered_prime HT (by decide : 2 < 7)
  have rightQ := entered_prime HT (by decide : 3 < 7)
  rw [← P.environment] at rightExponent rightP rightQ
  exact framed_trace (callEnvironment s) (call_valid HS) (callSp s)
    (inputExponent (callEnvironment s) s.mem)
    (inputPrime (callEnvironment s) s.mem 2) (inputPrime (callEnvironment s) s.mem 3)
    (inputPrime (callEnvironment s) t.mem 2) (inputPrime (callEnvironment s) t.mem 3)
    (P.release HS) _ _ _ _ _ _
    ⟨⟨I, J, entered_exponent HS, rightExponent.trans P.exponentValue.symm,
      entered_prime HS (by decide : 2 < 7), entered_prime HS (by decide : 3 < 7), rightP, rightQ⟩, P.stack⟩ A B

end VG.Proof.RsaKeyGen.X86.Key
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

theorem verified : Verified target VG.Impl.RsaKeyGen.X86.Key.code contract :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.RsaKeyGen.X86.Key
