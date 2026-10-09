import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop48
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Field48

/-!
# Interleaved counter mode and GHASH with AVX-512: the field

The only module of `Proof/Gcm/X86_64/StitchZ/` that computes in the field
(`Proof/Gcm/Poly.lean`), so that few modules import its algebra:

* `setup_ok`: the setup is `Stitch`'s (`Stitch.setup_ok`, which computes the
  powers in the field), and then the four lanes (`setupZ_ok`): the powers of
  the `k`-th load in lane `l` are `x · Pₖₗ = H¹⁶⁻⁴ᵏ⁻ˡ`.
* `finZ`: with those powers, the four lanes' products of a group, added and
  reduced, are `GHASH` over its sixteen blocks (`FinOk`); `powers48`: the
  powers `pow48` computes from them are those of 48 blocks, which
  `Field48.finZ48` turns into `FinOk48`.
* `stitch_ok`: both loops meet their contracts (`StitchOk`).
-/

namespace VG.Proof.Gcm.X86_64.StitchZ

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost StitchOk nb hk zero_xor_b ghash16)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB φ_reduceB)
open VG.Impl.Gcm.X86_64.StitchZ (ord setup enc dec)
open VG.Spec.Gcm (Block mul)

/-! ## The products of a group, in the field -/

/-- Sixteen blocks, in `Q`, the products in the lanes and order of a group. -/
theorem step16Z (H Y X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ X₁₀ X₁₁ X₁₂ X₁₃ X₁₄ X₁₅ T₁ T₂ T₃ T₄ T₅ T₆ T₇ T₈ T₉ T₁₀ T₁₁ T₁₂ T₁₃ T₁₄ T₁₅ T₁₆ : Block)
    (h₁ : x * φ T₁ = φ H) (h₂ : x * φ T₂ = φ H ^ 2) (h₃ : x * φ T₃ = φ H ^ 3) (h₄ : x * φ T₄ = φ H ^ 4) (h₅ : x * φ T₅ = φ H ^ 5) (h₆ : x * φ T₆ = φ H ^ 6) (h₇ : x * φ T₇ = φ H ^ 7) (h₈ : x * φ T₈ = φ H ^ 8) (h₉ : x * φ T₉ = φ H ^ 9) (h₁₀ : x * φ T₁₀ = φ H ^ 10) (h₁₁ : x * φ T₁₁ = φ H ^ 11) (h₁₂ : x * φ T₁₂ = φ H ^ 12) (h₁₃ : x * φ T₁₃ = φ H ^ 13) (h₁₄ : x * φ T₁₄ = φ H ^ 14) (h₁₅ : x * φ T₁₅ = φ H ^ 15) (h₁₆ : x * φ T₁₆ = φ H ^ 16) :
    (reduceB ((((Prod.zero.acc X₄ T₁₂).acc X₈ T₈).acc X₁₂ T₄).acc (Y ^^^ X₀) T₁₆) ^^^
        reduceB ((((Prod.zero.acc X₆ T₁₀).acc X₁₀ T₆).acc X₁₄ T₂).acc X₂ T₁₄)) ^^^
      (reduceB ((((Prod.zero.acc X₅ T₁₁).acc X₉ T₇).acc X₁₃ T₃).acc X₁ T₁₅) ^^^
        reduceB ((((Prod.zero.acc X₇ T₉).acc X₁₁ T₅).acc X₁₅ T₁).acc X₃ T₁₃)) =
      mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul ((Y ^^^ X₀)) H ^^^ X₁) H ^^^ X₂) H ^^^ X₃) H ^^^ X₄) H ^^^ X₅) H ^^^ X₆) H ^^^ X₇) H ^^^ X₈) H ^^^ X₉) H ^^^ X₁₀) H ^^^ X₁₁) H ^^^ X₁₂) H ^^^ X₁₃) H ^^^ X₁₄) H ^^^ X₁₅) H := by
  apply φ_inj
  simp only [φ_xor, φ_reduceB, Prod.val_acc, Prod.val_zero, φ_mul]
  linear_combination (φ Y + φ X₀) * h₁₆ + φ X₁ * h₁₅ + φ X₂ * h₁₄ + φ X₃ * h₁₃ + φ X₄ * h₁₂ + φ X₅ * h₁₁ + φ X₆ * h₁₀ + φ X₇ * h₉ + φ X₈ * h₈ + φ X₉ * h₇ + φ X₁₀ * h₆ + φ X₁₁ * h₅ + φ X₁₂ * h₄ + φ X₁₃ * h₃ + φ X₁₄ * h₂ + φ X₁₅ * h₁

/-- The four lanes' products of a group, added and reduced: `GHASH` over the
sixteen blocks. -/
theorem finZ_mul (H : Block) (X : Nat → Block) (P : Nat → Nat → Block) (yl : Nat → Block)
    (hy : ∀ l, 1 ≤ l → l < 4 → yl l = 0)
    (hP : ∀ k < 4, ∀ l < 4, x * φ (P k l) = φ H ^ (16 - 4 * k - l)) :
    yNew X P yl =
      mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul ((yl 0 ^^^ X 0)) H ^^^ X 1) H ^^^ X 2) H ^^^ X 3) H ^^^ X 4) H ^^^ X 5) H ^^^ X 6) H ^^^ X 7) H ^^^ X 8) H ^^^ X 9) H ^^^ X 10) H ^^^ X 11) H ^^^ X 12) H ^^^ X 13) H ^^^ X 14) H ^^^ X 15) H := by
  have h₁ := hP 3 (by decide) 3 (by decide)
  rw [show 16 - 4 * 3 - 3 = 1 from rfl, pow_one] at h₁
  have h₂ := hP 3 (by decide) 2 (by decide)
  have h₃ := hP 3 (by decide) 1 (by decide)
  have h₄ := hP 3 (by decide) 0 (by decide)
  have h₅ := hP 2 (by decide) 3 (by decide)
  have h₆ := hP 2 (by decide) 2 (by decide)
  have h₇ := hP 2 (by decide) 1 (by decide)
  have h₈ := hP 2 (by decide) 0 (by decide)
  have h₉ := hP 1 (by decide) 3 (by decide)
  have h₁₀ := hP 1 (by decide) 2 (by decide)
  have h₁₁ := hP 1 (by decide) 1 (by decide)
  have h₁₂ := hP 1 (by decide) 0 (by decide)
  have h₁₃ := hP 0 (by decide) 3 (by decide)
  have h₁₄ := hP 0 (by decide) 2 (by decide)
  have h₁₅ := hP 0 (by decide) 1 (by decide)
  have h₁₆ := hP 0 (by decide) 0 (by decide)
  simp only [Nat.reduceMul, Nat.reduceSub] at h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆
  simp only [yNew, accN, List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil, ord, inp, hy 1 (by decide) (by decide), hy 2 (by decide) (by decide),
    hy 3 (by decide) (by decide), ↓reduceIte, Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero,
    Nat.zero_add, Nat.add_zero, zero_xor_b]
  exact step16Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆

/-- The products of a group, for powers `x · Pₖₗ = H¹⁶⁻⁴ᵏ⁻ˡ`. -/
theorem finZ {H : Block} {P : Nat → Nat → Block} (hP : ∀ k < 4, ∀ l < 4, x * φ (P k l) = φ H ^ (16 - 4 * k - l)) :
    FinOk H P := fun X yl hy => by
  rw [ghash16]; exact finZ_mul H X P yl hy hP

/-- The powers of 48 blocks (`T48`), from those of sixteen. -/
theorem powers48 {H : Block} {P : Nat → Nat → Block}
    (hP : ∀ k < 4, ∀ l < 4, x * φ (P k l) = φ H ^ (16 - 4 * k - l)) :
    ∀ g < 3, ∀ k < 4, ∀ l < 4, x * φ (T48 P g k l) = φ H ^ (48 - 16 * g - 4 * k - l) := by
  intro g hg k hk l hl
  have h00 : x * φ (P 0 0) = φ H ^ 16 := hP 0 (by decide) 0 (by decide)
  rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2) with rfl | rfl | rfl
  · simp only [T48, Nat.reduceEqDiff, ↓reduceIte]
    rw [show 48 - 16 * 0 - 4 * k - l = (16 - 4 * k - l) + (16 + 16) by omega]
    exact φ_lanemul (hP k hk l hl) (φ_lanemul h00 h00)
  · simp only [T48, Nat.reduceEqDiff, ↓reduceIte]
    rw [show 48 - 16 * 1 - 4 * k - l = (16 - 4 * k - l) + 16 by omega]
    exact φ_lanemul (hP k hk l hl) h00
  · simp only [T48, ↓reduceIte]
    rw [show 48 - 16 * 2 - 4 * k - l = 16 - 4 * k - l by omega]
    exact hP k hk l hl

/-! ## Both loops -/

theorem setup_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (.block setup) s₀ fun s => ∃ P, Ready s₀ P s ∧
      ∀ k < 4, ∀ l < 4, x * φ (P k l) = φ (hk s₀) ^ (16 - 4 * k - l) := by
  rw [setup, WP.block_append_iff]
  exact WP.mono (Stitch.setup_ok hp) fun _ ⟨_, hR, hpw⟩ => WP.mono (setupZ_ok hR) fun _ hR' =>
    ⟨_, hR', fun k hk l hl => by
      rw [show 16 - 4 * k - l = 16 - 2 * (2 * k + l / 2) - l % 2 by omega]
      exact hpw _ (by omega) _ (by omega)⟩

/-- The encryption of `n` blocks (a multiple of 16, at least 16). -/
theorem enc_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) : WP isa enc s₀ (EPost s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨_, hR, hpw⟩ => encTail_ok hp hm (finZ hpw) (finZ48 (powers48 hpw)) hR)

/-- The decryption of `n` blocks (a multiple of 16, at least 16). -/
theorem dec_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) : WP isa dec s₀ (DPost s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨_, hR, hpw⟩ => decTail_ok hp hm (finZ hpw) (finZ48 (powers48 hpw)) hR)

/-- Both loops meet their contracts. -/
theorem stitch_ok : StitchOk Impl.Gcm.X86_64.StitchZ.enc Impl.Gcm.X86_64.StitchZ.dec :=
  ⟨fun _ hp hm => enc_ok hp hm, fun _ hp hm => dec_ok hp hm⟩

end VG.Proof.Gcm.X86_64.StitchZ
