module

public import VerifiedGarbage.Proof.Dsa.Arm.Key.Call
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Two
import VerifiedGarbage.Proof.Framework.Arm.RelCT

import VerifiedGarbage.Proof.Dsa.Arm.Key.Body
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheckCT
import VerifiedGarbage.Proof.Dsa.Arm.GenerateDerive
import VerifiedGarbage.Proof.Dsa.Arm.GenerateDeriveCT
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.Arm.Target

/-!
# The calls of key generation leak only what their contracts allow (32-bit ARM)

Two runs with the same public data and domain push the same words and call
`vg_dsa_check_parameters` with the same public arguments and domain
(`checkCall_ct`), and `vg_dsa_derive_key` with the same public arguments,
domain and status (`deriveCall_ct`), which their contracts' constant time
covers.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.GenerateKey

theorem pub_checkRd {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : checkRd s₁ = checkRd s₂ := by
  simp only [checkRd, rKeyR, pub_r3 e, pub_arg e 0 (by decide), pub_rLow e]

theorem pub_checkWr {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : checkWr s₁ = checkWr s₂ := by
  simp only [checkWr, rScratch, pub_arg e 5 (by decide), pub_arg e 6 (by decide)]

theorem pub_deriveRd {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : deriveRd s₁ = deriveRd s₂ := by
  simp only [deriveRd, nonceR, rKeyR, pub_r3 e, pub_arg e 0 (by decide), pub_arg e 2 (by decide),
    pub_rLow e, pub_rBase e]

theorem pub_deriveWr {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : deriveWr s₁ = deriveWr s₂ := by
  simp only [deriveWr, rOut, rScratch, pub_r0 e, pub_r1 e, pub_arg e 5 (by decide), pub_arg e 6 (by decide)]

/-- The domain the callee reads is the key's. -/
theorem params_call {s₀ u : State} (A : KeyABI s₀) (h : RReady s₀ u) (rd wr : List Region) :
    Spec.Rsa.bytesAt (callEntryOf rd wr u).mem (State.addr (s₀.gpr .r3)) (stackArg s₀ 0).toNat =
      (rInput s₀).key := by
  simp only [State.withRegions_mem, State.callEntry_mem]
  rw [rBytes_frame (call_push_frame A h) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (A.stackKey.sub_left (low_sub s₀ (by decide))).symm)
    (by have := (stackArg s₀ 0).isLt; omega), key_bytes A h]

theorem pushed_sp_eq {s₁ s₂ t₁ t₂ : State} (e : pubOf s₁ = pubOf s₂) (h₁ : RReady s₁ t₁) (h₂ : RReady s₂ t₂)
    (rd₁ wr₁ rd₂ wr₂ : List Region) : (callEntryOf rd₁ wr₁ t₁).sp = (callEntryOf rd₂ wr₂ t₂).sp := by
  show (pushed callPush t₁).sp = (pushed callPush t₂).sp
  rw [pushed_sp, pushed_sp, h₁.sp, h₂.sp, pub_sp e]

/-! ## The domain check -/

/-- Two runs about to call the check alike. -/
def CheckRel (t₁ t₂ : State) : Prop :=
  ∃ s₁ s₂, KeyABI s₁ ∧ KeyABI s₂ ∧ pubOf s₁ = pubOf s₂ ∧ (rInput s₁).key = (rInput s₂).key ∧
    RReady s₁ t₁ ∧ RReady s₂ t₂ ∧ CheckRegs s₁ t₁ ∧ CheckRegs s₂ t₂

theorem check_pub {s₁ s₂ t₁ t₂ : State} (A₁ : KeyABI s₁) (A₂ : KeyABI s₂) (e : pubOf s₁ = pubOf s₂)
    (hk : (rInput s₁).key = (rInput s₂).key) (h₁ : RReady s₁ t₁) (h₂ : RReady s₂ t₂) (C₁ : CheckRegs s₁ t₁)
    (C₂ : CheckRegs s₂ t₂) :
    checkArm.pub (callEntryOf (checkRd s₁) (checkWr s₁) t₁) (callEntryOf (checkRd s₂) (checkWr s₂) t₂) := by
  refine ⟨pushed_sp_eq e h₁ h₂ _ _ _ _, ?_, by rw [cc_r0 C₁, cc_r0 C₂, pub_r3 e],
    by rw [cc_r1 C₁, cc_r1 C₂, pub_arg e 0 (by decide)], by rw [cc_r2 C₁, cc_r2 C₂, pub_arg e 1 (by decide)],
    by rw [cc_r3 C₁, cc_r3 C₂, pub_arg e 2 (by decide)], fun i hi => ?_⟩
  · unfold checkParams
    rw [cc_r0 C₁, cc_r0 C₂, cc_r1 C₁, cc_r1 C₂, params_call A₁ h₁, params_call A₂ h₂, hk]
  · show stackArg _ i = stackArg _ i
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · rw [cc_a0 A₁ h₁ C₁, cc_a0 A₂ h₂ C₂, pub_arg e 5 (by decide)]
    · rw [cc_a1 A₁ h₁ C₁, cc_a1 A₂ h₂ C₂, pub_arg e 6 (by decide)]

theorem checkCall_ct (name : String) : RelCT isa CheckRel (callWith name Generate.checkParameters)
    fun _ _ => True := by
  unfold callWith
  refine RelCT.frame (fun t₁ t₂ ⟨s₁, s₂, _, _, e, _, h₁, h₂, _⟩ => by rw [h₁.sp, h₂.sp, pub_sp e]) ?_
  intro a b ta tb a' b' hp ea eb
  obtain ⟨t₁, t₂, ⟨s₁, s₂, A₁, A₂, e, hk, h₁, h₂, C₁, C₂⟩, p₁, p₂⟩ := hp
  rw [push_pushed (by decide) (call_sp_le A₁ h₁), Option.some.injEq] at p₁
  rw [push_pushed (by decide) (call_sp_le A₂ h₂), Option.some.injEq] at p₂
  subst p₁ p₂
  refine RelCT.call (P := fun x y => x = pushed callPush t₁ ∧ y = pushed callPush t₂) (k := checkArm)
    (fun s hs => let ⟨t, s', e, ha, hp⟩ := check_correct hs; ⟨t, s', e, ha, hp⟩) check_constantTime
    (checkRd s₁) (checkWr s₁) (fun _ _ ⟨r₁, r₂⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ ea eb
  subst r₁ r₂
  obtain ⟨c₁, w₁⟩ := check_covers A₁ h₁
  obtain ⟨c₂, w₂⟩ := check_covers A₂ h₂
  have p₂ : checkArm.pre (callEntryOf (checkRd s₂) (checkWr s₂) t₂) := check_call_pre A₂ h₂ C₂
  have pb := check_pub A₁ A₂ e hk h₁ h₂ C₁ C₂
  rw [← pub_checkRd e, ← pub_checkWr e] at p₂ c₂ pb
  rw [← pub_checkWr e] at w₂
  exact ⟨check_call_pre A₁ h₁ C₁, p₂, pb, c₁, w₁, c₂, w₂⟩

/-! ## The derivation -/

/-- Two runs about to call the derivation alike, with the same status. -/
def DeriveRel (t₁ t₂ : State) : Prop :=
  ∃ s₁ s₂, KeyABI s₁ ∧ KeyABI s₂ ∧ pubOf s₁ = pubOf s₂ ∧ (rInput s₁).key = (rInput s₂).key ∧
    RReady s₁ t₁ ∧ RReady s₂ t₂ ∧ DeriveRegs s₁ t₁ ∧ DeriveRegs s₂ t₂ ∧
    Spec.Dsa.signStatus (deriveResult s₁ t₁) = Spec.Dsa.signStatus (deriveResult s₂ t₂)

theorem derive_pub {s₁ s₂ t₁ t₂ : State} (A₁ : KeyABI s₁) (A₂ : KeyABI s₂) (e : pubOf s₁ = pubOf s₂)
    (hk : (rInput s₁).key = (rInput s₂).key) (h₁ : RReady s₁ t₁) (h₂ : RReady s₂ t₂) (C₁ : DeriveRegs s₁ t₁)
    (C₂ : DeriveRegs s₂ t₂)
    (hr : Spec.Dsa.signStatus (deriveResult s₁ t₁) = Spec.Dsa.signStatus (deriveResult s₂ t₂)) :
    deriveArm.pub (callEntryOf (deriveRd s₁) (deriveWr s₁) t₁)
      (callEntryOf (deriveRd s₂) (deriveWr s₂) t₂) := by
  refine ⟨pushed_sp_eq e h₁ h₂ _ _ _ _, ?_, by rw [dc_r0 C₁, dc_r0 C₂, pub_r0 e],
    by rw [dc_r1 C₁, dc_r1 C₂, pub_r1 e], by rw [dc_r2 C₁, dc_r2 C₂, pub_r3 e],
    by rw [dc_r3 C₁, dc_r3 C₂, pub_arg e 0 (by decide)], fun i hi => ?_⟩
  · unfold deriveLeak
    rw [deriveRes_call A₁ h₁ C₁, deriveRes_call A₂ h₂ C₂, hr]
    unfold deriveParams
    rw [dc_r2 C₁, dc_r2 C₂, dc_r3 C₁, dc_r3 C₂, params_call A₁ h₁, params_call A₂ h₂, hk]
  · show stackArg _ i = stackArg _ i
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    · rw [dc_a0 A₁ h₁ C₁, dc_a0 A₂ h₂ C₂, pub_arg e 1 (by decide)]
    · exact addr_inj32 (by rw [dc_a1 A₁ h₁ C₁, dc_a1 A₂ h₂ C₂, pub_rBase e])
    · rw [dc_a2 A₁ h₁ C₁, dc_a2 A₂ h₂ C₂, pub_arg e 2 (by decide)]
    · rw [dc_a3 A₁ h₁ C₁, dc_a3 A₂ h₂ C₂, pub_arg e 5 (by decide)]
    · rw [dc_a4 A₁ h₁ C₁, dc_a4 A₂ h₂ C₂, pub_arg e 6 (by decide)]

theorem deriveCall_ct (name : String) : RelCT isa DeriveRel (callWith name Generate.deriveKey)
    fun _ _ => True := by
  unfold callWith
  refine RelCT.frame (fun t₁ t₂ ⟨s₁, s₂, _, _, e, _, h₁, h₂, _⟩ => by rw [h₁.sp, h₂.sp, pub_sp e]) ?_
  intro a b ta tb a' b' hp ea eb
  obtain ⟨t₁, t₂, ⟨s₁, s₂, A₁, A₂, e, hk, h₁, h₂, C₁, C₂, hr⟩, p₁, p₂⟩ := hp
  rw [push_pushed (by decide) (call_sp_le A₁ h₁), Option.some.injEq] at p₁
  rw [push_pushed (by decide) (call_sp_le A₂ h₂), Option.some.injEq] at p₂
  subst p₁ p₂
  refine RelCT.call (P := fun x y => x = pushed callPush t₁ ∧ y = pushed callPush t₂) (k := deriveArm)
    (fun s hs => let ⟨t, s', e, ha, hp⟩ := derive_correct hs; ⟨t, s', e, ha, hp⟩) derive_constantTime
    (deriveRd s₁) (deriveWr s₁) (fun _ _ ⟨r₁, r₂⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ ea eb
  subst r₁ r₂
  obtain ⟨c₁, w₁⟩ := derive_covers A₁ h₁
  obtain ⟨c₂, w₂⟩ := derive_covers A₂ h₂
  have p₂ : deriveArm.pre (callEntryOf (deriveRd s₂) (deriveWr s₂) t₂) := derive_call_pre A₂ h₂ C₂
  have pb := derive_pub A₁ A₂ e hk h₁ h₂ C₁ C₂ hr
  rw [← pub_deriveRd e, ← pub_deriveWr e] at p₂ c₂ pb
  rw [← pub_deriveWr e] at w₂
  exact ⟨derive_call_pre A₁ h₁ C₁, p₂, pb, c₁, w₁, c₂, w₂⟩

end VG.Proof.Dsa.Arm.Key
