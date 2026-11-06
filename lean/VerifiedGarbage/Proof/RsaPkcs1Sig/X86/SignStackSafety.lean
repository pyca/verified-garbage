module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivateCall

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignNoSp
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignFnInput
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Rsa.X86.PrivFnInput

/-! # Stack bound and instruction safety for every CRT-backed signing variant -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Sign
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCode)

theorem code_noSp (v : CrtImpl) : NoSp (code (privName v) (privCode v)) := by
  intro i hi
  change i ∈ instrs (.frame (.push savedRegisters)
    (.seq (.frame (.alloc frameBytes) (body (privName v) (privCode v)) (.free frameBytes))
      (.block restore)) (.pop .ebx 4)) at hi
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · apply inner_noSp v i
    simpa only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] using hi
  · rfl

theorem code_sp (v : CrtImpl) :
    (code (privName v) (privCode v)).all (fun i => !isa.writesSp i) = true :=
  VG.Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp v)

end VG.Proof.RsaPkcs1Sig.X86.Sgn
