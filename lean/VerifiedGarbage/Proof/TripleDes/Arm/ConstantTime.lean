import VerifiedGarbage.Proof.TripleDes.Arm.FunctionsLit
import VerifiedGarbage.Proof.Framework.Arm.TaintMono

/-! # Constant-time Triple DES block and key-expansion programs -/

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm

/-- Only argument pointers and explicitly public integer parameters agree;
all memory contents, including the key, schedule, and data, may differ. -/
def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

/-! The analyses as summaries: the body of the loop of rounds, which each
block function runs three times (two of them in each direction), and the
block functions, which the ECB functions call. Both keep `r1`–`r3`, which
they do not write. -/

taint_summary roundEnc : taintS (Taint.ofRegs [.r0, .r1, .r2, .r9])
  (.block (roundBody ++ roundAdvance .encrypt)) keeping (Taint.ofRegs [.r1, .r2, .r3])
taint_summary roundDec : taintS (Taint.ofRegs [.r0, .r1, .r2, .r9])
  (.block (roundBody ++ roundAdvance .decrypt)) keeping (Taint.ofRegs [.r1, .r2, .r3])
taint_summary encSum : taintS (Taint.ofRegs [.r0, .r1, .r2]) encryptBlock
  keeping (Taint.ofRegs [.r1, .r2, .r3]) using roundEnc roundDec
taint_summary decSum : taintS (Taint.ofRegs [.r0, .r1, .r2]) decryptBlock
  keeping (Taint.ofRegs [.r1, .r2, .r3]) using roundEnc roundDec

theorem encryptBlock_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.r0, .r1, .r2]) encryptBlock := by
  obtain ⟨_, h⟩ := VG.Taint.exists_check_of_sumOk (τ := Taint.ofRegs [.r0, .r1, .r2]) encSum (by decide +kernel)
  refine VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.r0, .r1, .r2]) ?_ h
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

theorem decryptBlock_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.r0, .r1, .r2]) decryptBlock := by
  obtain ⟨_, h⟩ := VG.Taint.exists_check_of_sumOk (τ := Taint.ofRegs [.r0, .r1, .r2]) decSum (by decide +kernel)
  refine VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.r0, .r1, .r2]) ?_ h
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

theorem expandKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.r0, .r1, .r2, .r3]) Key.expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

theorem ecbEncrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.r0, .r1, .r2, .r3]) Ecb.encrypt := by
  obtain ⟨_, h⟩ : ∃ h, (taintS.check (Taint.ofRegs [.r0, .r1, .r2, .r3]) Ecb.encrypt h).isSome = true := by
    taint_decide_sum [encSum, decSum]
  refine VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ?_ h
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

theorem ecbDecrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.r0, .r1, .r2, .r3]) Ecb.decrypt := by
  obtain ⟨_, h⟩ : ∃ h, (taintS.check (Taint.ofRegs [.r0, .r1, .r2, .r3]) Ecb.decrypt h).isSome = true := by
    taint_decide_sum [encSum, decSum]
  refine VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ?_ h
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

end VG.Proof.TripleDes.Arm
