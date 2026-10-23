module
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CTDefs
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall

import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallResult

/-! # Domain-checking calls share their public parameters and arguments -/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom.CheckCall
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

theorem call_pub {s₁ s₂ t₁ t₂ : State} (A₁ : KeyABI s₁) (A₂ : KeyABI s₂) (e : pubOf s₁ = pubOf s₂)
    (h₁ : Ready s₁ t₁) (h₂ : Ready s₂ t₂) (C₁ : CallSlots s₁ t₁) (C₂ : CallSlots s₂ t₂) (rd wr : List Region)
    (hk : (rInput s₁).key.map (·.toNat) =
      (rInput s₂).key.map (·.toNat))
    :
    (Spec.Dsa.checkParametersContract abi 108).pub (t₁.callEntry.withRegions rd wr) (t₂.callEntry.withRegions rd wr) := by
  sig_pub [Spec.Dsa.checkParametersContract, Spec.Dsa.checkParametersSig, abi, argSlots, argVal, argBytes]
  simp only [ce_arg A₁ h₁ C₁ rd wr (show 0 < 6 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 1 < 6 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 2 < 6 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 3 < 6 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 4 < 6 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 5 < 6 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 0 < 6 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 1 < 6 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 2 < 6 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 3 < 6 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 4 < 6 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 5 < 6 by decide),
    callVal]
  have esp := esp_of_rf h₁.rf (pub_rBase e ▸ h₂.rf)
  rw [callEntry_bytes A₁ h₁ (A₁.stackKey.symm.sub_right (stk_sub s₁ (by decide))) (by omega),
    callEntry_bytes A₂ h₂ (A₂.stackKey.symm.sub_right (stk_sub s₂ (by decide))) (by omega)]
  have k₁ := callKey A₁ h₁
  have k₂ := callKey A₂ h₂
  simp only [argumentPointer] at k₁ k₂
  exact ⟨by rw [esp], by rw [k₁, k₂]; exact hk,
    pub_arg e 3 (by decide), pub_arg e 4 (by decide), pub_arg e 5 (by decide),
    pub_arg e 6 (by decide), pub_arg e 9 (by decide), pub_arg e 10 (by decide)⟩

theorem pub_callRd {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : callRd s₁ = callRd s₂ := by
  simp only [callRd, argRegion, argumentPointer, pub_arg e 3 (by decide), pub_arg e 4 (by decide)]

theorem pub_callWr {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : callWr s₁ = callWr s₂ := by
  simp only [callWr, argRegion, argumentPointer, pub_arg e 9 (by decide), pub_arg e 10 (by decide), pub_rLow e]

/-- The public domain bytes of the entry. -/
abbrev keyLeak (s₀ : State) : List Nat :=
  (rInput s₀).key.map (·.toNat)

/-- Two runs about to call the callee alike. -/
def CallRel (t₁ t₂ : State) : Prop :=
  ∃ s₁ s₂, KeyABI s₁ ∧ KeyABI s₂ ∧ pubOf s₁ = pubOf s₂ ∧ keyLeak s₁ = keyLeak s₂ ∧
    Ready s₁ t₁ ∧ Ready s₂ t₂ ∧ CallSlots s₁ t₁ ∧ CallSlots s₂ t₂

theorem call_ct (F : CheckFn) : RelCT isa CallRel (.call F.name F.code) fun _ _ => True := by
  intro t₁ t₂ u₁ u₂ v₁ v₂ hp x₁ x₂
  obtain ⟨s₁, s₂, A₁, A₂, e, hk, h₁, h₂, C₁, C₂⟩ := hp
  refine RelCT.call (P := fun x y => x = t₁ ∧ y = t₂) F.verified.1 F.verified.2.1 (callRd s₁) (callWr s₁)
    (fun _ _ ⟨r₁, r₂⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ x₁ x₂
  subst r₁ r₂
  obtain ⟨c₁, w₁⟩ := call_covers A₁ h₁
  obtain ⟨c₂, w₂⟩ := call_covers A₂ h₂
  have p₂ := call_pre A₂ h₂ C₂
  rw [← pub_callRd e, ← pub_callWr e] at p₂ c₂
  rw [← pub_callWr e] at w₂
  exact ⟨call_pre A₁ h₁ C₁, p₂, call_pub A₁ A₂ e h₁ h₂ C₁ C₂ _ _ hk, c₁, w₁, c₂, w₂,
    esp_of_rf h₁.rf (pub_rBase e ▸ h₂.rf)⟩

end VG.Proof.Dsa.X86.KeyRandom.CheckCall
