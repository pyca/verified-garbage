module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyABI
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPublicLeak
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.FrameTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallArgs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallValid
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSamples

/-! # Native key assembly is constant time under exactly the shared API's declared observations -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86
open VG.Proof.RsaKeyGen.X86.Key (contract public_inputs entry_input callSp entered_exponent entered_prime
  callEnvironment inputExponent inputPrime call_valid)

theorem constantTime : ConstantTime isa contract.pre contract.pub VG.Impl.RsaKeyGen.X86.KeyRuntime.code := by
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

end VG.Proof.RsaKeyGen.X86.KeyRuntime
