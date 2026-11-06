module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverPublicCall

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverNoSp
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverFnInput
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! # Stack bound and instruction safety for every CRT-backed signing variant -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Recover
open VG.Impl.RsaPkcs1Sig.X86.Verify (frameBytes)

theorem code_noSp (v : PublicImpl) : NoSp (code v.name v.code) := by
  intro i hi
  change i ∈ instrs (.frame (.push savedRegisters)
    (.seq (.frame (.alloc frameBytes) (body v.name v.code) (.free frameBytes))
      (.block VG.Impl.RsaPkcs1Sig.X86.Sign.restore)) (.pop .ebx 4)) at hi
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · apply inner_noSp v i
    simpa only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] using hi
  · rfl

theorem code_sp (v : PublicImpl) :
    (code v.name v.code).all (fun i => !isa.writesSp i) = true :=
  VG.Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp v)

end VG.Proof.RsaPkcs1Sig.X86.Rcv
