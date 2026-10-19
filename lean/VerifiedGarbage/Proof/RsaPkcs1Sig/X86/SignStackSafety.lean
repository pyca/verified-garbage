module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignVerified

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

theorem code_stack (v : CrtImpl) : stackUse (code (privName v) (privCode v)) ≤ sigStack := by
  have priv := VG.Proof.Rsa.X86.PrivChecked.code_stack v
  simp only [VG.Proof.Rsa.X86.PrivChecked.stackBytes] at priv
  have enc : stackUse VG.Impl.RsaPkcs1Sig.X86.encode = 0 := by decide +kernel
  have bound : stackUse (body (privName v) (privCode v)) ≤ 3392 := by
    simp only [body, afterEnc, zeroOut, wipe, stackUse, enc, Nat.max_le]
    repeat apply And.intro
    all_goals omega
  simp only [code, stackUse, VG.X86.frameBytes, List.length_cons, List.length_nil,
    VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes, sigStack]
  omega

end VG.Proof.RsaPkcs1Sig.X86.Sgn
