module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicCall

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyNoSp
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyFnInput
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! # Stack bound and instruction safety for every CRT-backed signing variant -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Verify

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

theorem code_stack (v : PublicImpl) : stackUse (code v.name v.code) ≤ verifyStack := by
  have pub := v.stack
  have enc : stackUse VG.Impl.RsaPkcs1Sig.X86.encode = 0 := by decide +kernel
  have cmp : stackUse VG.Impl.RsaPkcs1Sig.X86.compare = 0 := by decide +kernel
  have bound : stackUse (body v.name v.code) ≤ 100 := by
    simp only [body, afterPub, tail, ret0, stackUse, enc, cmp, Nat.max_le]
    repeat apply And.intro
    all_goals omega
  simp only [code, stackUse, VG.X86.frameBytes, List.length_cons, List.length_nil,
    VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes, verifyStack]
  omega

end VG.Proof.RsaPkcs1Sig.X86.Ver
