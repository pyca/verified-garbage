module

public import VerifiedGarbage.Proof.MillerRabin.X86.HeaderReady
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingLoop

/-! # Repeated squaring has a public iteration count and secret arithmetic -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86

theorem square_step_ct {σ₁ σ₂ : State} {base : Addr} {bytes w q : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) (hq : 0 < q ∧ q < 2 ^ 31) :
    RelCT isa (fun s t => SquareReady σ₁ base bytes w q s ∧ SquareReady σ₂ base bytes w q t) sqStep
      (fun s t => SquareReady σ₁ base bytes w (q - 1) s ∧ SquareReady σ₂ base bytes w (q - 1) t ∧
        s.zf = some (decide (q = 1)) ∧ t.zf = some (decide (q = 1))) := by
  have productCT := (C.multiply (o := 6) (a := 6) (b := 6) (by decide) (by decide) (by decide)
    square_args_cert).mono (P' := fun s t => SquareReady σ₁ base bytes w q s ∧ SquareReady σ₂ base bytes w q t)
    (fun _ _ ⟨h₁, h₂⟩ => ⟨⟨h₁.stage, h₁.reduced⟩, ⟨h₂.stage, h₂.reduced⟩⟩) (fun _ _ _ => trivial)
  have productPost := productCT.wp (F₁ := HeaderReady σ₁ base bytes w sQ q)
    (F₂ := HeaderReady σ₂ base bytes w sQ q) (fun _ _ ⟨h₁, h₂⟩ =>
      ⟨product_header_ready C.facts₁ ⟨h₁.stage, h₁.count⟩ (by decide) (by decide) (by decide)
        (.inr (.inl rfl)) (by decide) h₁.reduced,
       product_header_ready C.facts₂ ⟨h₂.stage, h₂.count⟩ (by decide) (by decide) (by decide)
        (.inr (.inl rfl)) (by decide) h₂.reduced⟩)
  have equalCT := (C.pieces equal_minus_cert).mono
    (P' := fun s t => True ∧ HeaderReady σ₁ base bytes w sQ q s ∧ HeaderReady σ₂ base bytes w sQ q t)
    (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁.stage, h₂.stage⟩) (fun _ _ _ => trivial)
  have equalPost := equalCT.wp (F₁ := HeaderReady σ₁ base bytes w sQ q)
    (F₂ := HeaderReady σ₂ base bytes w sQ q) (fun _ _ ⟨_, h₁, h₂⟩ =>
      ⟨equal_header_ready C.facts₁ h₁ (a := 6) (b := 8) (e := sE2) (by decide) (by decide)
        (by decide) (by decide) (by decide),
       equal_header_ready C.facts₂ h₂ (a := 6) (b := 8) (e := sE2) (by decide) (by decide)
        (by decide) (by decide) (by decide)⟩)
  have flagCT := (C.counter (k := q) (by omega) (by decide : sQ + 4 ≤ 1600) square_flag_cert).mono
    (P' := fun s t => True ∧ HeaderReady σ₁ base bytes w sQ q s ∧ HeaderReady σ₂ base bytes w sQ q t)
    (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩) (fun _ _ _ => trivial)
  have core : RelCT isa (fun s t => SquareReady σ₁ base bytes w q s ∧ SquareReady σ₂ base bytes w q t) sqStep
      (fun _ _ => True) := by
    unfold sqStep seqs
    simp only [List.foldr_cons, List.foldr_nil]
    exact productPost.seq (equalPost.seq (flagCT.seq (RelCT.nil (fun _ _ _ => trivial))))
  exact (core.wp (fun _ _ ⟨h₁, h₂⟩ => ⟨square_ready_step C.facts₁ h₁ hq, square_ready_step C.facts₂ h₂ hq⟩)).mono
    (fun _ _ h => h) (fun _ _ ⟨_, ⟨h₁, z₁⟩, ⟨h₂, z₂⟩⟩ => ⟨h₁, h₂, z₁, z₂⟩)

theorem square_loop_ct {σ₁ σ₂ : State} {base : Addr} {bytes w q0 : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) (hq : 0 < q0 ∧ q0 < 2 ^ 31) :
    RelCT isa (fun s t => SquareReady σ₁ base bytes w q0 s ∧ SquareReady σ₂ base bytes w q0 t) sqLoop
      (fun s t => SquareReady σ₁ base bytes w 0 s ∧ SquareReady σ₂ base bytes w 0 t) := by
  refine (count_loop_ct hq.1 (fun j s t => SquareReady σ₁ base bytes w (q0 - j) s ∧
    SquareReady σ₂ base bytes w (q0 - j) t) ?_).mono (fun _ _ h => h) ?_
  · intro j hj
    apply (square_step_ct C (q := q0 - j) ⟨by omega, by omega⟩).mono (fun _ _ h => h)
    rintro s t ⟨h₁, h₂, z₁, z₂⟩
    have count : q0 - j - 1 = q0 - (j + 1) := by omega
    have endEq : decide (q0 - j = 1) = decide (j + 1 = q0) := decide_eq_decide.mpr (by omega)
    exact ⟨⟨count ▸ h₁, count ▸ h₂⟩, by rw [z₁, endEq], by rw [z₂, endEq]⟩
  · intro s t h
    simpa only [Nat.sub_self] using h

end VG.Proof.MillerRabin.X86
