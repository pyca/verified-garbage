module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptVerified

/-! # Stack bound and instruction safety for precomputed encryption -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Impl.RsaPkcs1Enc.X86.Encrypt

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

theorem code_stack (v : PublicImpl) : stackUse (code v.name v.code) ≤ encryptStack := by
  have pub := v.stack
  have enc : stackUse encoding = 0 := by decide +kernel
  have tailBound : stackUse afterPub = 0 := by decide +kernel
  have bound : stackUse (body v.name v.code) ≤ 24 := by
    simp only [body, stackUse, enc, tailBound, Nat.max_le]
    repeat apply And.intro
    all_goals omega
  simp only [code, stackUse, VG.X86.frameBytes, List.length_cons, List.length_nil,
    VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes, encryptStack]
  omega

end VG.Proof.RsaPkcs1Enc.X86.Enc
