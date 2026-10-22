module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingContext

/-! # Reuse public buffer-copy timing while retaining workspace geometry -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86

theorem copy_stage_ct {σ₁ σ₂ : State} {base : Addr} {bytes w o a : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) (ho : o < 28) (ha : a < 28) (hne : a ≠ o)
    (mutable : o = 5 ∨ o = 6 ∨ o = 8 ∨ (11 ≤ o ∧ o < 27)) (cert : PieceCert (copy o a)) :
    RelCT isa (fun s t => Stage base bytes w σ₁ s ∧ Stage base bytes w σ₂ t) (copy o a)
      (fun s t => Stage base bytes w σ₁ s ∧ Stage base bytes w σ₂ t) := by
  exact ((C.pieces cert).wp (F₁ := Stage base bytes w σ₁) (F₂ := Stage base bytes w σ₂)
    (fun _ _ ⟨h₁, h₂⟩ =>
      ⟨WP.mono (h₁.copy C.facts₁.lower C.facts₁.upper C.facts₁.fit ho ha hne mutable C.facts₁.width)
        (fun _ ⟨_, ht, _, _⟩ => ht),
       WP.mono (h₂.copy C.facts₂.lower C.facts₂.upper C.facts₂.fit ho ha hne mutable C.facts₂.width)
        (fun _ ⟨_, ht, _, _⟩ => ht)⟩)).mono (fun _ _ h => h) (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩)

end VG.Proof.MillerRabin.X86
