module

import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
import VerifiedGarbage.Spec.RsaPkcs1Enc.Random

/-!
# The entropy a function asks for is public (#6400)

Of the specifications alone, whatever the implementations. A postcondition allows
more than one length of the next tape; two runs of an implementation of the RSA key
search that agree on what is public ask for the same one, since its `Api` says that
it is public (`Api.publicOut`), which every artifact proves.
-/

namespace VG.Test.EntropyRequest

open VG Spec.RsaKeyGen

/-- Both a tape of 2 octets and one of 3 may follow a result that leaves 1 octet. -/
example : Spec.Entropy.RequestValid 100 1 2 ∧ Spec.Entropy.RequestValid 100 1 3 := by
  unfold Spec.Entropy.RequestValid; decide

/-- The declarations of the functions whose tapes are secret. -/
example : keySearchApi.publicOut = some keySearchOut := rfl
example : Spec.RsaPkcs1Enc.encryptRandomApi.publicOut = some Spec.RsaPkcs1Enc.encryptRandomOut := rfl

/-- Two runs that agree on what is public ask for the same length, at `state[3]`. -/
theorem request_eq {M : ISA} {A : Abi M} {c : Prog M} {k : Contract M} (h : keySearchOut.Of A c k)
    {vals : M.State → List (BitVec 64)}
    (ha : A.args ((keySearchSig.words A.ptrBits).map (·.bits A.ptrBits)) = some vals)
    {s₁ s₂ s₁' s₂' : M.State} {t₁ t₂ : List Leak} {st₁ st₂ : Addr} {a₁ b₁ c₁ d₁ e₁ f₁ g₁ : BitVec 64}
    {a₂ b₂ c₂ d₂ e₂ f₂ g₂ : BitVec 64} (h₁ : vals s₁ = [a₁, b₁, c₁, d₁, e₁, f₁, g₁, st₁])
    (h₂ : vals s₂ = [a₂, b₂, c₂, d₂, e₂, f₂, g₂, st₂]) (p₁ : k.pre s₁) (p₂ : k.pre s₂) (hp : k.pub s₁ s₂)
    (r₁ : Exec M c s₁ t₁ s₁') (r₂ : Exec M c s₂ t₂ s₂') :
    (A.mem s₁').readW (st₁ + 24) 64 = (A.mem s₂').readW (st₂ + 24) 64 := by
  unfold PublicOut.Of at h
  rw [ha] at h
  have hg : ∀ vs m, Curry.apply (keySearchSig.words A.ptrBits) (keySearchOut.given A.ptrBits) vs m = [] := by
    intro vs m
    rcases vs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩ <;> rfl
  have := h s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ hp ((hg _ _).trans (hg _ _).symm) r₁ r₂
  rw [h₁, h₂] at this
  exact BitVec.eq_of_toNat_eq (List.cons.inj this).1

end VG.Test.EntropyRequest
