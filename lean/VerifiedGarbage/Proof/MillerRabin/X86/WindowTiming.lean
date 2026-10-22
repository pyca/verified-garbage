module

public import VerifiedGarbage.Proof.MillerRabin.X86.FourTiming
public import VerifiedGarbage.Proof.MillerRabin.X86.ScanTiming

/-! # A secret exponent digit changes values but not the round's trace -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86

theorem window_equal_ct {σ₁ σ₂ : State} {base : Addr} {bytes w k : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) (hk : k < 2 ^ 32) :
    RelCT isa (fun s t => HeaderReady σ₁ base bytes w sK k s ∧ HeaderReady σ₂ base bytes w sK k t)
      (.seq (equal sE1 aY aT0) (.seq (equal sE2 aY aM1) (.block winEnd))) (fun _ _ => True) := by
  have one := ((C.pieces equal_one_cert).mono
    (P' := fun s t => HeaderReady σ₁ base bytes w sK k s ∧ HeaderReady σ₂ base bytes w sK k t)
    (fun _ _ ⟨h₁, h₂⟩ => ⟨h₁.stage, h₂.stage⟩) (fun _ _ _ => trivial)).wp
    (F₁ := HeaderReady σ₁ base bytes w sK k) (F₂ := HeaderReady σ₂ base bytes w sK k)
    (fun _ _ ⟨h₁, h₂⟩ =>
      ⟨equal_header_ready C.facts₁ h₁ (a := 6) (b := 11) (e := sE1) (by decide) (by decide)
        (by decide) (by decide) (by decide),
       equal_header_ready C.facts₂ h₂ (a := 6) (b := 11) (e := sE1) (by decide) (by decide)
        (by decide) (by decide) (by decide)⟩)
  have minus := ((C.pieces equal_minus_cert).mono
    (P' := fun s t => True ∧ HeaderReady σ₁ base bytes w sK k s ∧ HeaderReady σ₂ base bytes w sK k t)
    (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁.stage, h₂.stage⟩) (fun _ _ _ => trivial)).wp
    (F₁ := HeaderReady σ₁ base bytes w sK k) (F₂ := HeaderReady σ₂ base bytes w sK k)
    (fun _ _ ⟨_, h₁, h₂⟩ =>
      ⟨equal_header_ready C.facts₁ h₁ (a := 6) (b := 8) (e := sE2) (by decide) (by decide)
        (by decide) (by decide) (by decide),
       equal_header_ready C.facts₂ h₂ (a := 6) (b := 8) (e := sE2) (by decide) (by decide)
        (by decide) (by decide) (by decide)⟩)
  exact one.seq (minus.seq ((C.counter hk (by decide : sK + 4 ≤ 1600) window_end_cert).mono
    (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩) (fun _ _ _ => trivial)))

theorem window_ct {σ₁ σ₂ : State} {base : Addr} {bytes w k : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) (hk : 0 < k ∧ k < 2 ^ 32) :
    RelCT isa (fun s t => WindowReady σ₁ base bytes w k s ∧ WindowReady σ₂ base bytes w k t) win
      (fun s t => WindowReady σ₁ base bytes w (k - 1) s ∧ WindowReady σ₂ base bytes w (k - 1) t ∧
        s.zf = some (decide ((k - 1) % 8 = 0)) ∧ t.zf = some (decide ((k - 1) % 8 = 0))) := by
  have scanCT := ((scan_ct C).mono
    (P' := fun s t => WindowReady σ₁ base bytes w k s ∧ WindowReady σ₂ base bytes w k t)
    (fun _ _ ⟨h₁, h₂⟩ => ⟨h₁.stage, h₂.stage⟩) (fun _ _ _ => trivial)).wp
    (fun _ _ ⟨h₁, h₂⟩ => ⟨scan_ready C.facts₁ h₁, scan_ready C.facts₂ h₂⟩)
  have productCT := ((C.multiply (o := 6) (a := 6) (b := 5) (by decide) (by decide) (by decide)
    digit_args_cert).mono
    (P' := fun s t => True ∧ SelectedReady σ₁ base bytes w k s ∧ SelectedReady σ₂ base bytes w k t)
    (fun _ _ ⟨_, h₁, h₂⟩ => ⟨⟨h₁.stage, h₁.selected⟩, ⟨h₂.stage, h₂.selected⟩⟩)
    (fun _ _ _ => trivial)).wp
    (F₁ := HeaderReady σ₁ base bytes w sK k) (F₂ := HeaderReady σ₂ base bytes w sK k)
    (fun _ _ ⟨_, h₁, h₂⟩ =>
      ⟨product_header_ready C.facts₁ ⟨h₁.stage, h₁.count⟩ (by decide) (by decide) (by decide)
        (.inr (.inl rfl)) (by decide) h₁.selected,
       product_header_ready C.facts₂ ⟨h₂.stage, h₂.count⟩ (by decide) (by decide) (by decide)
        (.inr (.inl rfl)) (by decide) h₂.selected⟩)
  have core : RelCT isa (fun s t => WindowReady σ₁ base bytes w k s ∧ WindowReady σ₂ base bytes w k t)
      win (fun _ _ => True) :=
    (four_squares_ct C).seq ((scanCT.seq productCT).seq ((window_equal_ct C hk.2).mono
      (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩) (fun _ _ _ => trivial)))
  exact (core.wp (fun _ _ ⟨h₁, h₂⟩ => ⟨window_ready_step C.facts₁ h₁ hk, window_ready_step C.facts₂ h₂ hk⟩)).mono
    (fun _ _ h => h) (fun _ _ ⟨_, ⟨h₁, z₁⟩, ⟨h₂, z₂⟩⟩ => ⟨h₁, h₂, z₁, z₂⟩)

end VG.Proof.MillerRabin.X86
