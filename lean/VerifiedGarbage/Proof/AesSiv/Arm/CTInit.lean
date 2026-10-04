import VerifiedGarbage.Proof.AesSiv.Arm.Init
import VerifiedGarbage.Proof.AesGcm.Arm.CTBase

/-!
# AES-SIV on ARMv7: `init` is constant time

Untrusted: everything here is checked by Lean. Two runs with the same
pointers, key length and stack pointer leak the same: the blocks between
the calls the taint analysis checks from the registers holding the
arguments (`initPre`) or what `init` keeps from them (the key, the half
length, the context and the scratch buffer, `IKeep`); the calls get the same
arguments in both runs (`ek_rel`, `sub_rel`).
-/

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm
open VG.Proof.AesGcm.Arm (CT)
open VG.Proof.CmacAes.Stream.Arm (EArgs SArgs ek_call sub_call ek_rel sub_rel)

/-- After the entry, in one run from `s₀`, whose stack pointer is `sp₀`. -/
def IK (sp₀ Kp Ct S : BitVec 32) (KL : Nat) (s : State) : Prop :=
  ∃ s₀ : State, s₀.sp = sp₀ ∧ IPre s₀ Kp Ct S KL ∧ IKeep s₀ Kp Ct S KL s

theorem IK.regs {sp₀ Kp Ct S : BitVec 32} {KL : Nat} {s₁ s₂ : State} (h₁ : IK sp₀ Kp Ct S KL s₁)
    (h₂ : IK sp₀ Kp Ct S KL s₂) : ∀ r ∈ ([.r4, .r5, .r6, .r11] : List Reg), s₁.gpr r = s₂.gpr r := by
  obtain ⟨_, _, _, k₁⟩ := h₁
  obtain ⟨_, _, _, k₂⟩ := h₂
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [k₁.r4, k₂.r4]
  · rw [k₁.r5, k₂.r5]
  · rw [k₁.r6, k₂.r6]
  · rw [k₁.r11, k₂.r11]

/-- After a call, which keeps the callee-saved registers. -/
theorem IK.call {sp₀ Kp Ct S : BitVec 32} {KL : Nat} {s s' : State} (h : IK sp₀ Kp Ct S KL s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : IK sp₀ Kp Ct S KL s' :=
  let ⟨s₀, e, hp, k⟩ := h
  ⟨s₀, e, hp, k.call hg hsp hrd hwr⟩

theorem init_ct' {sp₀ Kp Ct S : BitVec 32} {KL : Nat} :
    CT (fun s => s.sp = sp₀ ∧ IPre s Kp Ct S KL) init := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r0, .r1, .r2, .r3])
      (.block initPre) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r4, .r5, .r6, .r11])
      (.block initMid₁) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r4, .r5, .r6, .r11])
      (.block initMid₂) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hD⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r11])
      (.block initPost) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.seq (J := fun s => IK sp₀ Kp Ct S KL s ∧ EArgs s Kp Ct S (KL / 2))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.2.r0, h₂.2.r0]
      · exact BitVec.eq_of_toNat_eq (by rw [h₁.2.r1, h₂.2.r1])
      · rw [h₁.2.r2, h₂.2.r2]
      · rw [h₁.2.r3, h₂.2.r3]) hA)
    (fun s h => WP.mono (initPre_wp h.2) fun s' ⟨k, _, e⟩ => ⟨⟨s, h.1, h.2, k⟩, e⟩) ?_
  refine CT.seq (J := IK sp₀ Kp Ct S KL) (ek_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2⟩)
    (fun s h => WP.mono (ek_call h.2) fun s' p => h.1.call p.saved p.sp p.rd p.wr) ?_
  refine CT.seq (J := fun s => IK sp₀ Kp Ct S KL s ∧ SArgs s Ct (Ct + BitVec.ofNat 32 240) S (KL / 8 + 6))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ => h₁.regs h₂) hB)
    (fun s ⟨s₀, e, hp, k⟩ => WP.mono (initMid₁_wp hp k) fun s' ⟨k', _, a⟩ => ⟨⟨s₀, e, hp, k'⟩, a⟩) ?_
  refine CT.seq (J := IK sp₀ Kp Ct S KL)
    (sub_rel (sp₀ := sp₀) fun s₁ s₂ hh => by
      obtain ⟨⟨⟨_, e₁, _, k₁⟩, a₁⟩, ⟨⟨_, e₂, _, k₂⟩, a₂⟩⟩ := hh
      exact ⟨a₁, a₂, k₁.sp.trans e₁, k₂.sp.trans e₂⟩)
    (fun s h => WP.mono (sub_call h.2) fun s' p => h.1.call p.saved p.sp p.rd p.wr) ?_
  refine CT.seq (J := fun s => IK sp₀ Kp Ct S KL s ∧
      EArgs s (Kp + BitVec.ofNat 32 (KL / 2)) (Ct + BitVec.ofNat 32 272) S (KL / 2))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ => h₁.regs h₂) hC)
    (fun s ⟨s₀, e, hp, k⟩ => WP.mono (initMid₂_wp hp k) fun s' ⟨k', _, a⟩ => ⟨⟨s₀, e, hp, k'⟩, a⟩) ?_
  refine CT.seq (J := IK sp₀ Kp Ct S KL) (ek_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2⟩)
    (fun s h => WP.mono (ek_call h.2) fun s' p => h.1.call p.saved p.sp p.rd p.wr) ?_
  exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h₁.regs h₂ _ (by simp)) hD

theorem init_ct : ConstantTime isa initArm.pre initArm.pub init := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp₂ : IPre s₂ (s₁.gpr .r0) (s₁.gpr .r2) (s₁.gpr .r3) (s₁.gpr .r1).toNat := by
    rw [q2, q3, q4, q5]; exact IPre.of h₂
  exact (init_ct' (sp₀ := s₁.sp) _ _ _ _ _ _ ⟨⟨rfl, IPre.of h₁⟩, ⟨q1.symm, hp₂⟩⟩ e₁ e₂).1

end VG.Proof.AesSiv.Arm
