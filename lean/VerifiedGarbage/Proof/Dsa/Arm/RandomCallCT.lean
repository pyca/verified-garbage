module
public import VerifiedGarbage.Proof.Dsa.Arm.RandomCall
public import VerifiedGarbage.Proof.Dsa.Arm.RandomTwo

import VerifiedGarbage.Proof.Dsa.Arm.SignCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.RandomAttempt
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Framework.Arm.RelCT

/-!
# The signer's call leaks only what its contract allows (32-bit ARM)

Two runs push the same public words and call `vg_dsa_sign` with the same
public arguments, public key bytes and signing status (`call_pub`), which
its contract's constant time covers (`callSigner_ct`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign

theorem pub_callRd {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : callRd s₁ = callRd s₂ := by
  simp only [callRd, nonceR, rKeyR, rDigestR, pub_r3 e, pub_arg e 0 (by decide), pub_arg e 2 (by decide),
    pub_arg e 3 (by decide), pub_arg e 4 (by decide), pub_rLow e, pub_rBase e]

theorem pub_callWr {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : callWr s₁ = callWr s₂ := by
  simp only [callWr, rOut, rScratch, pub_r0 e, pub_r1 e, pub_arg e 7 (by decide), pub_arg e 8 (by decide)]

/-- What the signer may leak: the public key bytes and its status. -/
theorem signLeak_call {s₀ u : State} (A : RandomABI s₀) (h : RReady s₀ u) (C : CallRegs s₀ u) :
    signLeak (callEntryOf s₀ u) = keyLeak s₀ ++ [Spec.Dsa.signStatus (callResult s₀ u)] := by
  have hf := call_push_frame A h
  have ek : Spec.Rsa.bytesAt (pushed callPush u).mem (State.addr (s₀.gpr .r3)) (stackArg s₀ 0).toNat =
      (rInput s₀).key := by
    rw [rBytes_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (A.stackKey.sub_left (low_sub s₀ (by decide))).symm)
      (by have := (stackArg s₀ 0).isLt; omega), callKey A h]
  unfold signLeak
  rw [signRes_call A h C]
  simp only [State.withRegions_mem, State.callEntry_mem, ce_r2 C, ce_r3 C, ce_a0 A h C, ce_a2 A h C, ek]
  rfl

/-- Two runs about to call the signer alike. -/
def CallRel (t₁ t₂ : State) : Prop :=
  ∃ s₁ s₂, RandomABI s₁ ∧ RandomABI s₂ ∧ pubOf s₁ = pubOf s₂ ∧ keyLeak s₁ = keyLeak s₂ ∧
    RReady s₁ t₁ ∧ RReady s₂ t₂ ∧ CallRegs s₁ t₁ ∧ CallRegs s₂ t₂ ∧
    Spec.Dsa.signStatus (callResult s₁ t₁) = Spec.Dsa.signStatus (callResult s₂ t₂)

theorem call_pub {s₁ s₂ t₁ t₂ : State} (A₁ : RandomABI s₁) (A₂ : RandomABI s₂) (e : pubOf s₁ = pubOf s₂)
    (hk : keyLeak s₁ = keyLeak s₂) (h₁ : RReady s₁ t₁) (h₂ : RReady s₂ t₂) (C₁ : CallRegs s₁ t₁)
    (C₂ : CallRegs s₂ t₂)
    (hr : Spec.Dsa.signStatus (callResult s₁ t₁) = Spec.Dsa.signStatus (callResult s₂ t₂)) :
    signArm.pub (callEntryOf s₁ t₁) (callEntryOf s₂ t₂) := by
  have r11 := r11_of_rf h₁.rf (pub_rBase e ▸ h₂.rf)
  have ea : ∀ i (hi : i < 8), stackArg (callEntryOf s₁ t₁) i = t₁.gpr callPush[i] ∧
      stackArg (callEntryOf s₂ t₂) i = t₂.gpr callPush[i] :=
    fun i hi => ⟨callEntry_arg A₁ h₁ hi, callEntry_arg A₂ h₂ hi⟩
  refine ⟨?_, by rw [signLeak_call A₁ h₁ C₁, signLeak_call A₂ h₂ C₂, hk, hr], by rw [ce_r0 C₁, ce_r0 C₂, pub_r0 e],
    by rw [ce_r1 C₁, ce_r1 C₂, pub_r1 e], by rw [ce_r2 C₁, ce_r2 C₂, pub_r3 e],
    by rw [ce_r3 C₁, ce_r3 C₂, pub_arg e 0 (by decide)], fun i hi => ?_⟩
  · show (pushed callPush t₁).sp = (pushed callPush t₂).sp
    rw [pushed_sp, pushed_sp, h₁.sp, h₂.sp, pub_sp e]
  · show stackArg (callEntryOf s₁ t₁) i = stackArg (callEntryOf s₂ t₂) i
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
      omega
    · rw [(ea 0 (by decide)).1, (ea 0 (by decide)).2]
      exact C₁.r4.trans ((pub_arg e 1 (by decide)).trans C₂.r4.symm)
    · rw [(ea 1 (by decide)).1, (ea 1 (by decide)).2]
      exact C₁.r5.trans (by rw [r11]; exact C₂.r5.symm)
    · rw [(ea 2 (by decide)).1, (ea 2 (by decide)).2]
      exact C₁.r6.trans ((pub_arg e 2 (by decide)).trans C₂.r6.symm)
    · rw [(ea 3 (by decide)).1, (ea 3 (by decide)).2]
      exact C₁.r7.trans ((pub_arg e 3 (by decide)).trans C₂.r7.symm)
    · rw [(ea 4 (by decide)).1, (ea 4 (by decide)).2]
      exact C₁.r8.trans ((pub_arg e 4 (by decide)).trans C₂.r8.symm)
    · rw [(ea 5 (by decide)).1, (ea 5 (by decide)).2]
      exact C₁.r9.trans ((pub_arg e 7 (by decide)).trans C₂.r9.symm)
    · rw [(ea 6 (by decide)).1, (ea 6 (by decide)).2]
      exact C₁.r10.trans ((pub_arg e 8 (by decide)).trans C₂.r10.symm)

theorem callSigner_ct (name : String) : RelCT isa CallRel (callSigner name (Entry.operation true))
    fun _ _ => True := by
  unfold callSigner
  refine RelCT.frame (fun t₁ t₂ ⟨s₁, s₂, _, _, e, _, h₁, h₂, _⟩ => by rw [h₁.sp, h₂.sp, pub_sp e]) ?_
  intro a b ta tb a' b' hp ea eb
  obtain ⟨t₁, t₂, ⟨s₁, s₂, A₁, A₂, e, hk, h₁, h₂, C₁, C₂, hr⟩, p₁, p₂⟩ := hp
  rw [push_pushed (by decide) (call_sp_le A₁ h₁), Option.some.injEq] at p₁
  rw [push_pushed (by decide) (call_sp_le A₂ h₂), Option.some.injEq] at p₂
  subst p₁ p₂
  refine RelCT.call (P := fun x y => x = pushed callPush t₁ ∧ y = pushed callPush t₂) (k := signArm)
    (fun s hs => let ⟨t, s', e, ha, hp⟩ := sign_correct hs; ⟨t, s', e, ha, hp⟩) sign_constantTime
    (callRd s₁) (callWr s₁) (fun _ _ ⟨r₁, r₂⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ ea eb
  subst r₁ r₂
  obtain ⟨c₁, w₁⟩ := call_covers A₁ h₁
  obtain ⟨c₂, w₂⟩ := call_covers A₂ h₂
  have p₂ : signArm.pre ((pushed callPush t₂).callEntry.withRegions (callRd s₂) (callWr s₂)) := call_pre A₂ h₂ C₂
  have pb : signArm.pub ((pushed callPush t₁).callEntry.withRegions (callRd s₁) (callWr s₁))
      ((pushed callPush t₂).callEntry.withRegions (callRd s₂) (callWr s₂)) := call_pub A₁ A₂ e hk h₁ h₂ C₁ C₂ hr
  rw [← pub_callRd e, ← pub_callWr e] at p₂ c₂ pb
  rw [← pub_callWr e] at w₂
  exact ⟨call_pre A₁ h₁ C₁, p₂, pb, c₁, w₁, c₂, w₂⟩

end VG.Proof.Dsa.Arm
