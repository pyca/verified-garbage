module
public import VerifiedGarbage.Proof.Dsa.X86.RandomCTDefs
public import VerifiedGarbage.Proof.Dsa.X86.RandomCall

import VerifiedGarbage.Proof.Dsa.X86.RandomAttempt
import VerifiedGarbage.Proof.Framework.Offset
import Batteries.Logic

/-!
# The signer's call leaks only what its contract allows (x86)

Two runs call `vg_dsa_sign` with the same public arguments, public key
bytes and signing status (`call_pub`), which its contract's constant time
covers (`call_ct`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random

theorem call_pub {s₁ s₂ t₁ t₂ : State} (A₁ : RandomSignABI s₁) (A₂ : RandomSignABI s₂) (e : pubOf s₁ = pubOf s₂)
    (h₁ : Ready s₁ t₁) (h₂ : Ready s₂ t₂) (C₁ : CallSlots s₁ t₁) (C₂ : CallSlots s₂ t₂) (rd wr : List Region)
    (hk : Spec.Dsa.publicBytesLeak (rInput s₁).pLen (rInput s₁).qLen (rInput s₁).key =
      Spec.Dsa.publicBytesLeak (rInput s₂).pLen (rInput s₂).qLen (rInput s₂).key)
    (hr : Spec.Dsa.signStatus (callResult s₁ t₁) = Spec.Dsa.signStatus (callResult s₂ t₂)) :
    (Spec.Dsa.signContract abi 108).pub (t₁.callEntry.withRegions rd wr) (t₂.callEntry.withRegions rd wr) := by
  sig_pub [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes]
  simp only [ce_arg A₁ h₁ C₁ rd wr (show 0 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 1 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 2 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 3 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 4 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 5 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 6 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 7 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 8 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 9 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 10 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 0 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 1 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 2 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 3 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 4 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 5 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 6 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 7 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 8 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 9 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 10 < 11 by decide),
    callVal, esp_ptr h₁ (d := oNonce) (by decide), esp_ptr h₂ (d := oNonce) (by decide),
    show 24 + oNonce = 112 from rfl]
  have hql₁ := rQBytes_le A₁
  have hqn₁ := rQBytes_length A₁
  have hql₂ := rQBytes_le A₂
  have hqn₂ := rQBytes_length A₂
  have esp := esp_of_rf h₁.rf (pub_rBase e ▸ h₂.rf)
  rw [callEntry_bytes A₁ h₁ (A₁.stackKeyWide.symm.sub_right (stk_sub s₁ (by decide))) (by omega),
    callEntry_bytes A₁ h₁ ((Offset.disjoint _ (by omega) (by omega) (by omega) :
      Region.Disjoint ⟨off (rLow s₁) 20, 4⟩ ⟨off (rLow s₁) 112, (X86.arg s₁ 6).toNat⟩).symm) (by omega),
    callEntry_bytes A₁ h₁ (A₁.stackDigestWide.symm.sub_right (stk_sub s₁ (by decide))) (by omega),
    callEntry_bytes A₂ h₂ (A₂.stackKeyWide.symm.sub_right (stk_sub s₂ (by decide))) (by omega),
    callEntry_bytes A₂ h₂ ((Offset.disjoint _ (by omega) (by omega) (by omega) :
      Region.Disjoint ⟨off (rLow s₂) 20, 4⟩ ⟨off (rLow s₂) 112, (X86.arg s₂ 6).toNat⟩).symm) (by omega),
    callEntry_bytes A₂ h₂ (A₂.stackDigestWide.symm.sub_right (stk_sub s₂ (by decide))) (by omega)]
  have k₁ := callKey A₁ h₁
  have k₂ := callKey A₂ h₂
  simp only [argumentPointer] at k₁ k₂
  refine ⟨by rw [esp], congrArg₂ (fun x y => x ++ [y]) (by rw [k₁, k₂]; exact hk) hr,
    pub_arg e 0 (by decide), pub_arg e 1 (by decide), pub_arg e 3 (by decide), pub_arg e 4 (by decide),
    pub_arg e 5 (by decide), by rw [esp], pub_arg e 6 (by decide), pub_arg e 7 (by decide),
    pub_arg e 8 (by decide), pub_arg e 11 (by decide), pub_arg e 12 (by decide)⟩

theorem pub_callRd {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : callRd s₁ = callRd s₂ := by
  simp only [callRd, argRegion, argumentPointer, pub_arg e 3 (by decide), pub_arg e 4 (by decide),
    pub_arg e 6 (by decide), pub_arg e 7 (by decide), pub_arg e 8 (by decide), pub_rLow e]

theorem pub_callWr {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : callWr s₁ = callWr s₂ := by
  simp only [callWr, argRegion, argumentPointer, pub_arg e 0 (by decide), pub_arg e 1 (by decide),
    pub_arg e 11 (by decide), pub_arg e 12 (by decide), pub_rLow e]

/-- The public key bytes of the entry. -/
abbrev keyLeak (s₀ : State) : List Nat :=
  Spec.Dsa.publicBytesLeak (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key

/-- Two runs about to call the signer alike. -/
def CallRel (t₁ t₂ : State) : Prop :=
  ∃ s₁ s₂, RandomSignABI s₁ ∧ RandomSignABI s₂ ∧ pubOf s₁ = pubOf s₂ ∧ keyLeak s₁ = keyLeak s₂ ∧
    Ready s₁ t₁ ∧ Ready s₂ t₂ ∧ CallSlots s₁ t₁ ∧ CallSlots s₂ t₂ ∧
    Spec.Dsa.signStatus (callResult s₁ t₁) = Spec.Dsa.signStatus (callResult s₂ t₂)

theorem call_ct (F : SignFn) : RelCT isa CallRel (.call F.name F.code) fun _ _ => True := by
  intro t₁ t₂ u₁ u₂ v₁ v₂ hp x₁ x₂
  obtain ⟨s₁, s₂, A₁, A₂, e, hk, h₁, h₂, C₁, C₂, hr⟩ := hp
  refine RelCT.call (P := fun x y => x = t₁ ∧ y = t₂) F.verified.1 F.verified.2.1 (callRd s₁) (callWr s₁)
    (fun _ _ ⟨r₁, r₂⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ x₁ x₂
  subst r₁ r₂
  obtain ⟨c₁, w₁⟩ := call_covers A₁ h₁
  obtain ⟨c₂, w₂⟩ := call_covers A₂ h₂
  have p₂ := call_pre A₂ h₂ C₂
  rw [← pub_callRd e, ← pub_callWr e] at p₂ c₂
  rw [← pub_callWr e] at w₂
  exact ⟨call_pre A₁ h₁ C₁, p₂, call_pub A₁ A₂ e h₁ h₂ C₁ C₂ _ _ hk hr, c₁, w₁, c₂, w₂,
    esp_of_rf h₁.rf (pub_rBase e ▸ h₂.rf)⟩

end VG.Proof.Dsa.X86
