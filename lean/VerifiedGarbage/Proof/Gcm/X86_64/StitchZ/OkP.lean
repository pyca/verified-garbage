module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZHTo
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Cvt
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop48
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop48To
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZC.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Prepared
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGKs
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZC
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.OutOfPlace
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Loop
import VerifiedGarbage.Proof.Framework.X86_64.HighKeep
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemD
import VerifiedGarbage.Proof.Gcm.Powers
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop48
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.SetupFin
public import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop48
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Ghash
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.OnePass
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.PhaseOne
public import VerifiedGarbage.Proof.Gcm.Poly
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Group

/-! ### `Gcm.X86_64.StitchZ.Ok`, which this module and modules that import it used -/

section

/-! ### `Gcm.X86_64.StitchZ.Field48`, which this module and modules that import it used -/

section

/-!
# Interleaved counter mode and GHASH with AVX-512: 48 blocks in the field

`finZ48`: with powers `x · T g k l = H⁴⁸⁻¹⁶ᵍ⁻⁴ᵏ⁻ˡ`, the products of 48 blocks
added and reduced as `body48` does are `GHASH` over them (`FinOk48`); and
`φ_lanemul`: the products `pow48` stores are the powers it says.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZ
open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB φ_reduceB)
open VG.Spec.Gcm (Block mul ghashFrom)

/-- A product of two powers, reduced, is their product. -/
theorem φ_lanemul {H a b : Block} {i j : Nat} (ha : x * φ a = φ H ^ i) (hb : x * φ b = φ H ^ j) :
    x * φ (reduceB (Prod.zero.acc a b)) = φ H ^ (i + j) := by
  rw [φ_reduceB, Prod.val_acc, Prod.val_zero, pow_add, ← ha, ← hb]; ring

/-- The products of 48 blocks, for powers `x · T g k l = H⁴⁸⁻¹⁶ᵍ⁻⁴ᵏ⁻ˡ`. -/
theorem finZ48 {H : Block} {T : Nat → Nat → Nat → Block}
    (hT : ∀ g < 3, ∀ k < 4, ∀ l < 4, x * φ (T g k l) = φ H ^ (48 - 16 * g - 4 * k - l)) : FinOk48 H T := by
  intro X yl hy
  obtain h000 := hT 0 (by decide) 0 (by decide) 0 (by decide)
  obtain h001 := hT 0 (by decide) 0 (by decide) 1 (by decide)
  obtain h002 := hT 0 (by decide) 0 (by decide) 2 (by decide)
  obtain h003 := hT 0 (by decide) 0 (by decide) 3 (by decide)
  obtain h010 := hT 0 (by decide) 1 (by decide) 0 (by decide)
  obtain h011 := hT 0 (by decide) 1 (by decide) 1 (by decide)
  obtain h012 := hT 0 (by decide) 1 (by decide) 2 (by decide)
  obtain h013 := hT 0 (by decide) 1 (by decide) 3 (by decide)
  obtain h020 := hT 0 (by decide) 2 (by decide) 0 (by decide)
  obtain h021 := hT 0 (by decide) 2 (by decide) 1 (by decide)
  obtain h022 := hT 0 (by decide) 2 (by decide) 2 (by decide)
  obtain h023 := hT 0 (by decide) 2 (by decide) 3 (by decide)
  obtain h030 := hT 0 (by decide) 3 (by decide) 0 (by decide)
  obtain h031 := hT 0 (by decide) 3 (by decide) 1 (by decide)
  obtain h032 := hT 0 (by decide) 3 (by decide) 2 (by decide)
  obtain h033 := hT 0 (by decide) 3 (by decide) 3 (by decide)
  obtain h100 := hT 1 (by decide) 0 (by decide) 0 (by decide)
  obtain h101 := hT 1 (by decide) 0 (by decide) 1 (by decide)
  obtain h102 := hT 1 (by decide) 0 (by decide) 2 (by decide)
  obtain h103 := hT 1 (by decide) 0 (by decide) 3 (by decide)
  obtain h110 := hT 1 (by decide) 1 (by decide) 0 (by decide)
  obtain h111 := hT 1 (by decide) 1 (by decide) 1 (by decide)
  obtain h112 := hT 1 (by decide) 1 (by decide) 2 (by decide)
  obtain h113 := hT 1 (by decide) 1 (by decide) 3 (by decide)
  obtain h120 := hT 1 (by decide) 2 (by decide) 0 (by decide)
  obtain h121 := hT 1 (by decide) 2 (by decide) 1 (by decide)
  obtain h122 := hT 1 (by decide) 2 (by decide) 2 (by decide)
  obtain h123 := hT 1 (by decide) 2 (by decide) 3 (by decide)
  obtain h130 := hT 1 (by decide) 3 (by decide) 0 (by decide)
  obtain h131 := hT 1 (by decide) 3 (by decide) 1 (by decide)
  obtain h132 := hT 1 (by decide) 3 (by decide) 2 (by decide)
  obtain h133 := hT 1 (by decide) 3 (by decide) 3 (by decide)
  obtain h200 := hT 2 (by decide) 0 (by decide) 0 (by decide)
  obtain h201 := hT 2 (by decide) 0 (by decide) 1 (by decide)
  obtain h202 := hT 2 (by decide) 0 (by decide) 2 (by decide)
  obtain h203 := hT 2 (by decide) 0 (by decide) 3 (by decide)
  obtain h210 := hT 2 (by decide) 1 (by decide) 0 (by decide)
  obtain h211 := hT 2 (by decide) 1 (by decide) 1 (by decide)
  obtain h212 := hT 2 (by decide) 1 (by decide) 2 (by decide)
  obtain h213 := hT 2 (by decide) 1 (by decide) 3 (by decide)
  obtain h220 := hT 2 (by decide) 2 (by decide) 0 (by decide)
  obtain h221 := hT 2 (by decide) 2 (by decide) 1 (by decide)
  obtain h222 := hT 2 (by decide) 2 (by decide) 2 (by decide)
  obtain h223 := hT 2 (by decide) 2 (by decide) 3 (by decide)
  obtain h230 := hT 2 (by decide) 3 (by decide) 0 (by decide)
  obtain h231 := hT 2 (by decide) 3 (by decide) 1 (by decide)
  obtain h232 := hT 2 (by decide) 3 (by decide) 2 (by decide)
  obtain h233 := hT 2 (by decide) 3 (by decide) 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceSub] at *
  apply φ_inj
  simp only [yNew48, acc48, List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil, pa, inp48, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, and_self, and_false,
    Nat.one_ne_zero, false_and, ↓reduceIte, Nat.reduceEqDiff, hy 1 (by decide) (by decide), hy 2 (by decide) (by decide),
    hy 3 (by decide) (by decide), Stitch.zero_xor_b, φ_xor, φ_reduceB, Prod.val_acc, Prod.val_zero,
    ghashFrom, List.map_append, List.map_cons, List.map_nil, φ_mul]
  linear_combination (φ (yl 0) + φ (X 0)) * h000 + φ (X 1) * h001 + φ (X 2) * h002 + φ (X 3) * h003 + φ (X 4) * h010 + φ (X 5) * h011 + φ (X 6) * h012 + φ (X 7) * h013 + φ (X 8) * h020 + φ (X 9) * h021 + φ (X 10) * h022 + φ (X 11) * h023 + φ (X 12) * h030 + φ (X 13) * h031 + φ (X 14) * h032 + φ (X 15) * h033 + φ (X 16) * h100 + φ (X 17) * h101 + φ (X 18) * h102 + φ (X 19) * h103 + φ (X 20) * h110 + φ (X 21) * h111 + φ (X 22) * h112 + φ (X 23) * h113 + φ (X 24) * h120 + φ (X 25) * h121 + φ (X 26) * h122 + φ (X 27) * h123 + φ (X 28) * h130 + φ (X 29) * h131 + φ (X 30) * h132 + φ (X 31) * h133 + φ (X 32) * h200 + φ (X 33) * h201 + φ (X 34) * h202 + φ (X 35) * h203 + φ (X 36) * h210 + φ (X 37) * h211 + φ (X 38) * h212 + φ (X 39) * h213 + φ (X 40) * h220 + φ (X 41) * h221 + φ (X 42) * h222 + φ (X 43) * h223 + φ (X 44) * h230 + φ (X 45) * h231 + φ (X 46) * h232 + φ (X 47) * h233

end VG.Proof.Gcm.X86_64.StitchZ

end

end

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

@[expose] public section

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
  rcases (by omega_using [hg] : g = 0 ∨ g = 1 ∨ g = 2) with rfl | rfl | rfl
  · simp only [T48, Nat.reduceEqDiff, ↓reduceIte]
    rw [show 48 - 16 * 0 - 4 * k - l = (16 - 4 * k - l) + (16 + 16) by omega_using [hk, hl]]
    exact φ_lanemul (hP k hk l hl) (φ_lanemul h00 h00)
  · simp only [T48, Nat.reduceEqDiff, ↓reduceIte]
    rw [show 48 - 16 * 1 - 4 * k - l = (16 - 4 * k - l) + 16 by omega_using [hk, hl]]
    exact φ_lanemul (hP k hk l hl) h00
  · simp only [T48, ↓reduceIte]
    rw [show 48 - 16 * 2 - 4 * k - l = 16 - 4 * k - l by omega_using []]
    exact hP k hk l hl

/-! ## Both loops -/

theorem setup_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (.block setup) s₀ fun s => ∃ P, Ready s₀ P s ∧
      ∀ k < 4, ∀ l < 4, x * φ (P k l) = φ (hk s₀) ^ (16 - 4 * k - l) := by
  rw [setup, WP.block_append_iff]
  exact WP.mono (Stitch.setup_ok hp) fun _ ⟨_, hR, hpw⟩ => WP.mono (setupZ_ok hR) fun _ hR' =>
    ⟨_, hR', fun k hk l hl => by
      rw [show 16 - 4 * k - l = 16 - 2 * (2 * k + l / 2) - l % 2 by omega_using []]
      exact hpw _ (by omega_using [hk, hl]) _ (by omega_using [])⟩

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

end

end

/-! ### `Gcm.X86_64.Cached.PreparedTo`, which only this module used -/

section

/-! # Prepared tables and the cached-key loop setup -/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZHTo
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPreTo CtxMode kp pp hk nr sch nb)
open VG.Proof.Gcm.X86_64.StitchZ (FinOk FinOk48)
open VG.Proof.Gcm.X86_64.StitchZTo (ReadyTo EInvTo AInvTo.pow)
open VG.Proof.Gcm.X86_64.StitchZR (ctx_keep powP48_ok)
open VG.Proof.Gcm.X86_64.StitchZRTo (setupPTo_ok)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF)
open VG.Impl.Gcm.X86_64.StitchZ (tab)
open VG.Impl.Gcm.X86_64.StitchZHTo (bigPTo)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Gcm (Block)

theorem ready_frame {s₀ s t : State} {P : Nat → Nat → Block} (h : ReadyTo s₀ P s)
    (f : ZFrame [] s t) : ReadyTo s₀ P t :=
  ⟨h.a.zframe f (by simp) (by simp) (by simp), by rw [f.gpr]; exact h.rdx,
    by rw [f.gpr]; exact h.rax, fun r h1 h2 h3 h4 => by rw [f.gpr]; exact h.gpr r h1 h2 h3 h4,
    fun k hk l hl => by rw [f.mem]; exact h.pw k hk l hl,
    fun l hl => by rw [f.zlane _ (by simp) l hl]; exact h.m1 l hl,
    by rw [f.zlane _ (by simp) 0 (by decide)]; exact h.y,
    fun l h1 h4 => by rw [f.zlane _ (by simp) l h4]; exact h.y1 l h1 h4⟩

theorem setup_ok {s₀ : State} (hp : SPreTo CtxMode.prepared s₀) :
    WP isa (.seq (.block Impl.Gcm.X86_64.StitchZRTo.setupP) Impl.Aes.X86_64.VaesZH.loadKeys) s₀ fun s =>
      ∃ P : Nat → Nat → Block, ReadyTo s₀ P s ∧
        (∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l))) ∧
        VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s := by
  refine WP.seq (WP.mono (setupPTo_ok hp) fun s ⟨P, hR, hpw⟩ => ?_)
  refine WP.mono (VG.Proof.Aes.X86_64.VaesZH.loadKeys_ok s (hR.a.keys hp) hp.rounds
    (by rw [hR.a.rsi]; simp)
    (by rw [hR.a.r10, hR.a.rdi])) fun t ⟨hK, hf⟩ => ?_
  exact ⟨P, ready_frame hR hf, hpw, hK⟩

theorem bigPTo_ok {s₀ : State} (hp : SPreTo CtxMode.prepared s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hP : ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)))
    (hFin : ∀ T : Nat → Nat → Nat → Block,
      (∀ g < 3, ∀ k < 4, ∀ l < 4, T g k l = hInvF (Spec.Gcm.hpow (hk s₀) (48 - 16 * g - 4 * k - l))) →
        FinOk48 (hk s₀) T) (h96 : 96 ≤ nb s₀) {s : State}
    (hI : EInvTo s₀ P 1 s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) : WP isa bigPTo s fun s' => ∃ e, EInvTo s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  have hP' := hp.toPrepared
  have hdi : s.gpr .rdi = kp s₀ := hI.gpr .rdi (by decide) (by decide) (by decide) (by decide) (by decide)
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hpw, hH⟩ := ctx_keep hP' hI.a.frame
  refine WP.seq (WP.mono (WP.hkeep (by decide +kernel) (powP48_ok hP' hdi hr11 hI.a.rd hI.a.wr hpw
    (fun l hl => by rw [← State.zlane_lt2 _ _ hl]; exact hI.a.msk l (by omega_using [hl])) hI.m1))
    fun s₁ ⟨⟨t, pm, keep, fr, g₁, rd₁, wr₁, z₁⟩, hh₁⟩ => ?_)
  rw [hH] at t
  let T : Nat → Nat → Nat → Block := fun g k l =>
    if g = 2 then P k l else s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128
  have hv : ∀ g < 3, ∀ k < 4, ∀ l < 4,
      s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l := fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2
      simp only [T, ↓reduceIte, show tab 2 + 64 * k + 16 * l = 64 * k + 16 * l by simp only [tab]; omega_using []]
      exact (keep (64 * k + 16 * l) (by omega_using [hk, hl])).trans (hI.pw k hk l hl)
    · simp only [T, h2, ↓reduceIte]
  have hT : FinOk48 (hk s₀) T := hFin T fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2; simp only [T, ↓reduceIte]; rw [hP k hk l hl]
    · simp only [T, h2, ↓reduceIte]; exact t g (by omega_using [hg, h2]) k hk l hl
  have hA₁ := (hI.a.pow hp fr g₁ rd₁ wr₁ fun r h7 h8 h9 h10 _ h12 l hl => z₁ r h7 h8 h9 h10 h12 l hl)
  exact (bigRestTo_ok hp hf hT (fun k l => by simp only [T, ↓reduceIte]) h96 hI
    hA₁ hv pm g₁
    (fun l hl => z₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl)
    (hCache.keep hh₁ (hA₁.keys hp)))

/-- `StitchZH.midC`, out of place. -/
theorem midCTo_ok {s₀ : State} (hp : SPreTo CtxMode.prepared s₀) {P : Nat → Nat → Block}
    (hr : StitchZH.RemOkG (hk s₀) P)
    (hP : ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)))
    (hFin : ∀ T : Nat → Nat → Nat → Block,
      (∀ g < 3, ∀ k < 4, ∀ l < 4, T g k l = hInvF (Spec.Gcm.hpow (hk s₀) (48 - 16 * g - 4 * k - l))) →
        FinOk48 (hk s₀) T) {s : State}
    (hR : ReadyTo s₀ P s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (Impl.Gcm.X86_64.StitchZH.midC true) s (Stitch.EPostTo s₀) := by
  have hP' := hp.toPrepared
  have hdi : s.gpr .rdi = kp s₀ := hR.a.rdi
  have hr11 : s.gpr .r11 = pp s₀ := hR.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hpw, hH⟩ := ctx_keep hP' hR.a.frame
  refine WP.seq (WP.mono (WP.hkeep (by decide +kernel) (powP48_ok hP' hdi hr11 hR.a.rd hR.a.wr hpw
    (fun l hl => by rw [← State.zlane_lt2 _ _ hl]; exact hR.a.msk l (by omega_using [hl])) hR.m1))
    fun s₁ ⟨⟨t, pm, keep, fr, g₁, rd₁, wr₁, z₁⟩, hh₁⟩ => ?_)
  rw [hH] at t
  let T : Nat → Nat → Nat → Block := fun g k l =>
    if g = 2 then P k l else s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128
  have hv : ∀ g < 3, ∀ k < 4, ∀ l < 4,
      s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l := fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2
      simp only [T, ↓reduceIte, show tab 2 + 64 * k + 16 * l = 64 * k + 16 * l by simp only [tab]; omega_using []]
      exact (keep (64 * k + 16 * l) (by omega_using [hk, hl])).trans (hR.pw k hk l hl)
    · simp only [T, h2, ↓reduceIte]
  have hT : FinOk48 (hk s₀) T := hFin T fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2; simp only [T, ↓reduceIte]; rw [hP k hk l hl]
    · simp only [T, h2, ↓reduceIte]; exact t g (by omega_using [hg, h2]) k hk l hl
  have hA₁ := (hR.a.pow hp fr g₁ rd₁ wr₁ fun r h7 h8 h9 h10 _ h12 l hl => z₁ r h7 h8 h9 h10 h12 l hl)
  exact WP.mono (StitchZC.midRestM_ok hp.toM (hp.k_c.symm.sub_right (Region.sub_prefix CtxMode.prepared.ge)) hp.s_c
    hr hT (fun k l => by simp only [T, ↓reduceIte]) hp.nb16 (hR.toM hp) (hA₁.toM hp) hv pm g₁
    (fun l hl => z₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl)
    (hCache.keep hh₁ (hA₁.keys hp))) fun _ h => h.toEPostTo

/-- `StitchZH.bigS`, out of place. -/
theorem bigSTo_ok {s₀ : State} (hp : SPreTo CtxMode.prepared s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hP : ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)))
    (hFin : ∀ T : Nat → Nat → Nat → Block,
      (∀ g < 3, ∀ k < 4, ∀ l < 4, T g k l = hInvF (Spec.Gcm.hpow (hk s₀) (48 - 16 * g - 4 * k - l))) →
        FinOk48 (hk s₀) T) {s : State}
    (hI : EInvTo s₀ P 1 s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) : WP isa (Impl.Gcm.X86_64.StitchZH.bigS true) s fun s' => ∃ e, EInvTo s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  have hP' := hp.toPrepared
  have hdi : s.gpr .rdi = kp s₀ := hI.gpr .rdi (by decide) (by decide) (by decide) (by decide) (by decide)
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hpw, hH⟩ := ctx_keep hP' hI.a.frame
  refine WP.seq (WP.mono (WP.hkeep (by decide +kernel) (powP48_ok hP' hdi hr11 hI.a.rd hI.a.wr hpw
    (fun l hl => by rw [← State.zlane_lt2 _ _ hl]; exact hI.a.msk l (by omega_using [hl])) hI.m1))
    fun s₁ ⟨⟨t, pm, keep, fr, g₁, rd₁, wr₁, z₁⟩, hh₁⟩ => ?_)
  rw [hH] at t
  let T : Nat → Nat → Nat → Block := fun g k l =>
    if g = 2 then P k l else s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128
  have hv : ∀ g < 3, ∀ k < 4, ∀ l < 4,
      s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l := fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2
      simp only [T, ↓reduceIte, show tab 2 + 64 * k + 16 * l = 64 * k + 16 * l by simp only [tab]; omega_using []]
      exact (keep (64 * k + 16 * l) (by omega_using [hk, hl])).trans (hI.pw k hk l hl)
    · simp only [T, h2, ↓reduceIte]
  have hT : FinOk48 (hk s₀) T := hFin T fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2; simp only [T, ↓reduceIte]; rw [hP k hk l hl]
    · simp only [T, h2, ↓reduceIte]; exact t g (by omega_using [hg, h2]) k hk l hl
  have hA₁ := (hI.a.pow hp fr g₁ rd₁ wr₁ fun r h7 h8 h9 h10 _ h12 l hl => z₁ r h7 h8 h9 h10 h12 l hl)
  exact WP.mono (StitchZC.bigSelM_ok hp.toM hf hT (fun k l => by simp only [T, ↓reduceIte]) (hI.toM hp)
    (hA₁.toM hp) hv pm g₁
    (fun l hl => z₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl)
    (hCache.keep hh₁ (hA₁.keys hp))) fun _ ⟨e, h, hk⟩ => ⟨e, h.toTo, hk⟩

end VG.Proof.Gcm.X86_64.StitchZHTo

end

end

/-! ### `Gcm.X86_64.StitchZTo.LoopP`, which only this module used -/

section

/-!
# The out-of-place AVX-512 loop, with the powers in the key context

Untrusted: everything here is checked by Lean. `bigPTo_ok`: `StitchZTo.bigPTo`
is `bigRestTo_ok` after `StitchZP.powP48`, which stores the tables of 48
blocks converted from the powers of the key context (`StitchZP.powP48_ok`,
for the in-place view `dst s₀`, whose key context the loop keeps:
`StitchZP.ctx_keep`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPreTo CtxMode kp pp nb hk)
open VG.Proof.Gcm.X86_64.StitchZ (FinOk FinOk48)
open VG.Proof.Gcm.X86_64.StitchZP (powP48_ok ctx_keep hInvF)
open VG.Impl.Gcm.X86_64.StitchZ (tab)
open VG.Impl.Gcm.X86_64.StitchZTo (bigPTo)
open VG.Spec.Gcm (Block)

/-- `bigPTo`: `bigTo` with the tables loaded. -/
theorem bigPTo_ok {s₀ : State} (hp : SPreTo CtxMode.powers s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hP : ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)))
    (hFin : ∀ T : Nat → Nat → Nat → Block,
      (∀ g < 3, ∀ k < 4, ∀ l < 4, T g k l = hInvF (Spec.Gcm.hpow (hk s₀) (48 - 16 * g - 4 * k - l))) →
        FinOk48 (hk s₀) T) (h96 : 96 ≤ nb s₀) {s : State}
    (hI : EInvTo s₀ P 1 s) : WP isa bigPTo s fun s' => ∃ e, EInvTo s₀ P e s' := by
  have hP' := hp.toP
  have hdi : s.gpr .rdi = kp s₀ := hI.gpr .rdi (by decide) (by decide) (by decide) (by decide) (by decide)
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hpw, hH⟩ := ctx_keep hP' hI.a.frame
  refine WP.seq (WP.mono (powP48_ok hP' hdi hr11 hI.a.rd hI.a.wr hpw
    (fun l hl => by rw [← State.zlane_lt2 _ _ hl]; exact hI.a.msk l (by omega_using [hl])) hI.m1)
    fun s₁ ⟨t, pm, keep, fr, g₁, rd₁, wr₁, z₁⟩ => ?_)
  rw [hH] at t
  let T : Nat → Nat → Nat → Block := fun g k l =>
    if g = 2 then P k l else s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128
  have hv : ∀ g < 3, ∀ k < 4, ∀ l < 4,
      s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l := fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2
      simp only [T, ↓reduceIte, show tab 2 + 64 * k + 16 * l = 64 * k + 16 * l by simp only [tab]; omega_using []]
      exact (keep (64 * k + 16 * l) (by omega_using [hk, hl])).trans (hI.pw k hk l hl)
    · simp only [T, h2, ↓reduceIte]
  have hT : FinOk48 (hk s₀) T := hFin T fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2; simp only [T, ↓reduceIte]; rw [hP k hk l hl]
    · simp only [T, h2, ↓reduceIte]; exact t g (by omega_using [hg, h2]) k hk l hl
  exact (bigRestTo_ok hp hf hT (fun k l => by simp only [T, ↓reduceIte]) h96 hI
    (hI.a.pow hp fr g₁ rd₁ wr₁ fun r h7 h8 h9 h10 _ h12 l hl => z₁ r h7 h8 h9 h10 h12 l hl) hv pm g₁
    fun l hl => z₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl)

end VG.Proof.Gcm.X86_64.StitchZTo

end

end


/-!
# The AVX-512 loops with the powers in the key context: both meet their contracts

Untrusted: everything here is checked by Lean. `stitchP_ok`: `StitchZP.enc`
and `StitchZP.dec` meet `StitchOkP`: the setup leaves the state of
`StitchZ.setup_ok` from the powers of the key context (`setupP_ok`): in the
field, `x · (Hⁿ · x⁻¹) = Hⁿ` (`x_φ_hInvF`, `φ_hpow`), so that their products,
and those of the tables loaded (`bigP_ok`, `bigDP_ok`), add up to `GHASH`
(`StitchZ.finZ`, `finZ48`); the rest is `StitchZ`'s (`encTailG_ok`,
`decTailG_ok`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZP

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch (nb SPreP StitchOkP EPost DPost hk)
open VG.Proof.Gcm.X86_64.StitchZ (finZ finZ48 FinOk48 encTailG_ok decTailG_ok)
open VG.Spec.Gcm (Block hpow)

/-- `Hⁿ · x⁻¹`, times `x`, is `Hⁿ`. -/
theorem x_φ_hInvF (H : Block) (n : Nat) : x * φ (hInvF (hpow H n)) = φ H ^ n := by
  rw [hInvF, Pclmul.x_φ_hInv, φ_hpow]

theorem finP {H : Block} {P : Nat → Nat → Block}
    (hP : ∀ k < 4, ∀ l < 4, P k l = hInvF (hpow H (16 - 4 * k - l))) :
    ∀ k < 4, ∀ l < 4, x * φ (P k l) = φ H ^ (16 - 4 * k - l) := fun k hk l hl => by
  rw [hP k hk l hl, x_φ_hInvF]

theorem fin48P (H : Block) (T : Nat → Nat → Nat → Block)
    (hT : ∀ g < 3, ∀ k < 4, ∀ l < 4, T g k l = hInvF (hpow H (48 - 16 * g - 4 * k - l))) : FinOk48 H T :=
  finZ48 fun g hg k hk l hl => by rw [hT g hg k hk l hl, x_φ_hInvF]

/-- The encryption of `n` blocks (a multiple of 16, at least 16). -/
theorem enc_ok {s₀ : State} (hp : SPreP s₀) (hm : nb s₀ % 16 = 0) : WP isa Impl.Gcm.X86_64.StitchZP.enc s₀ (EPost s₀) :=
  WP.seq (WP.mono (setupP_ok hp) fun _ ⟨_, hR, hpw⟩ =>
    encTailG_ok hp.base hm (finZ (finP hpw))
      144 (by decide) (by decide) (fun _ h hI => bigP_ok hp (finZ (finP hpw)) hpw (fin48P (hk s₀)) (Nat.le_trans (by decide) h) hI) hR)

/-- The decryption of `n` blocks (a multiple of 16, at least 16). -/
theorem dec_ok {s₀ : State} (hp : SPreP s₀) (hm : nb s₀ % 16 = 0) : WP isa Impl.Gcm.X86_64.StitchZP.dec s₀ (DPost s₀) :=
  WP.seq (WP.mono (setupP_ok hp) fun _ ⟨_, hR, hpw⟩ =>
    decTailG_ok hp.base hm (finZ (finP hpw)) 96 (by decide) (by decide) (fun _ h96 hI => bigDP_ok hp hpw (fin48P (hk s₀)) h96 hI) hR)

/-- Both loops meet their contracts. -/
theorem stitchP_ok : StitchOkP Impl.Gcm.X86_64.StitchZP.enc Impl.Gcm.X86_64.StitchZP.dec :=
  ⟨fun _ hp hm => enc_ok hp hm, fun _ hp hm => dec_ok hp hm⟩

end VG.Proof.Gcm.X86_64.StitchZP

/-! ## The out-of-place AVX-512 loops (`StitchZTo`): they meet their contract

Untrusted: everything here is checked by Lean. `stitchTo_ok`:
`StitchZTo.enc` meets `StitchToOkM` for a key context of either kind (it
computes the powers itself, from the hash subkey in the first 256 bytes):
the powers `H'`–`H'¹⁶` as `Stitch.setupG_ok` computes them (`setupGTo_ok`),
stored, and the rest of the setup (`setupTTo_ok`, `setupZTo_ok`); with them
the products of a group, and of 48 blocks, add up to `GHASH`
(`StitchZ.finZ`, `StitchZ.powers48`, `StitchZ.finZ48`), and the loops do the
rest (`encTailGTo_ok`, `bigTo_ok`).

`stitchToP_ok`: `StitchZTo.encP` meets `StitchToOkM` for a key context with
the powers: its setup loads them as `StitchZP.setupGP_ok` (`setupGPTo_ok`,
from the conversions of `StitchZP.cvtRun_ok` for the in-place view
`dst s₀`), then stores them and makes the rest of the setup as
`StitchZTo.enc`; with them and the tables of `bigPTo` the products add up to
`GHASH` (`StitchZP.finP`, `StitchZP.fin48P`).

They are proven here, with the loops they build on, rather than in
`Proof/Gcm/X86_64/StitchZTo/`, which does not compute in the field
(`Proof/Gcm/Poly.lean`), so that no more modules import its algebra.
-/

namespace VG.Proof.Gcm.X86_64.StitchZTo

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch (nb SPreTo StitchToOkM CtxMode hk in_sub_int)
open VG.Proof.Gcm.X86_64.Pclmul (mul_ok const_ok ldrev_ok hInv_ok rev_eq)
open VG.Proof.Gcm.X86_64.Vpclmul (powersYP_ok powers16P_ok)
open VG.Proof.Gcm.X86_64.StitchZ (finZ finZ48 powers48)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (setupG)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Impl.Gcm.X86_64.StitchZTo (setup enc encWith)

/-- `Stitch.setupG_ok`, from `SPreTo`. -/
theorem setupGTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) :
    WP isa (.block setupG) s₀ fun s =>
      (∀ l < 2, s.lane .xmm0 l = revMask) ∧ (∀ l < 2, s.lane .xmm1 l = poly) ∧
      (∀ k < 8, ∀ l < 2, x * φ (s.lane (preg16 k) l) = φ (hk s₀) ^ (16 - 2 * k - l)) ∧
      (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have hge := M.ge
  simp only [setupG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s₀ (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .rdi 240 s₂ (by decide)
    (by rw [o₂.xmm _ (by decide), c₁, rev_eq])
    (by rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr _ (by decide)]; exact in_sub_int hp.k_in (by omega_using [hge]))) fun s₃ ⟨l₃, o₃⟩ => ?_
  have o₁₃ := o₁₂.trans o₃
  rw [WP.block_append_iff]
  refine WP.mono (hInv_ok s₃) fun s₄ ⟨t₄, o₄⟩ => ?_
  have hH : x * φ (s₄.xmm .xmm3) = φ (hk s₀) := by
    rw [t₄, l₃, o₁₂.mem, o₁₂.gpr _ (by decide), BitVec.ofInt_natCast]; rfl
  rw [WP.block_append_iff]
  refine WP.mono (mul_ok .xmm4 .xmm3 .xmm3 s₄ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), c₂])) fun s₇ ⟨m₇, o₇⟩ => ?_
  have hH2 : x * φ (s₇.xmm .xmm4) = φ (hk s₀) ^ 2 := by
    rw [m₇, show ∀ a : Q, x * (x * a * a) = (x * a) * (x * a) from fun a => by ring, hH, pow_two]
  have o₁₇ := o₁₃.trans (o₄.trans o₇)
  rw [WP.block_append_iff]
  refine WP.mono (powersYP_ok (H := hk s₀)
    (by rw [(o₂.trans (o₃.trans (o₄.trans o₇))).xmm _ (by decide), c₁, rev_eq])
    (by rw [(o₃.trans (o₄.trans o₇)).xmm _ (by decide), c₂])
    (by rw [o₇.xmm _ (by decide), hH]) hH2)
    fun s₈ ⟨l0, l1, _, pw8, g₈, m₈, rd₈, wr₈⟩ => ?_
  refine WP.mono (powers16P_ok l1 pw8) fun s₉ ⟨pw, F⟩ => ⟨fun l hl => ?_, fun l hl => ?_, pw,
    fun r hr => by rw [F.gpr, g₈ r hr, o₁₇.gpr r hr], by rw [F.mem, m₈, o₁₇.mem],
    by rw [F.rd, rd₈, o₁₇.rd], by rw [F.wr, wr₈, o₁₇.wr]⟩
  · rw [F.lane _ (by decide) l hl]; exact l0 l hl
  · rw [F.lane _ (by decide) l hl]; exact l1 l hl

/-- The setup: the state the loop starts from, with the powers
`x · Pₖₗ = H¹⁶⁻⁴ᵏ⁻ˡ` in the working space. -/
theorem setupTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) :
    WP isa (.block setup) s₀ fun s => ∃ P, ReadyTo s₀ P s ∧
      ∀ k < 4, ∀ l < 4, x * φ (P k l) = φ (hk s₀) ^ (16 - 4 * k - l) := by
  rw [setup, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setupGTo_ok hp) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  exact WP.mono (setupTTo_ok hp l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR => WP.mono (setupZTo_ok hR) fun _ hR' =>
    ⟨_, hR', fun k hk l hl => by
      rw [show 16 - 4 * k - l = 16 - 2 * (2 * k + l / 2) - l % 2 by omega_using []]
      exact pw _ (by omega_using [hk, hl]) _ (by omega_using [])⟩

/-- The out-of-place loop meets its contract, for a key context of either
kind. -/
theorem stitchTo_ok (M : CtxMode) : StitchToOkM M Impl.Gcm.X86_64.StitchZTo.enc := fun _ hp hm =>
  WP.seq (WP.mono (setupTo_ok hp) fun _ ⟨_, hR, hpw⟩ =>
    encTailGTo_ok hp hm (finZ hpw) 256 (by decide) (by decide) (fun _ h hI => bigTo_ok hp (finZ hpw) (finZ48 (powers48 hpw)) (Nat.le_trans (by decide) h) hI) hR)

open VG.Proof.Gcm.X86_64.StitchZP (vinsSelf_ok consts_ok cvtRun_ok hInvF finP fin48P)
open VG.Impl.Gcm.X86_64.StitchZP (setupGP)
open VG.Impl.Gcm.X86_64.StitchZTo (setupP)

/-- `StitchZP.setupGP_ok`, from `SPreTo`. -/
theorem setupGPTo_ok {s₀ : State} (hp : SPreTo CtxMode.powers s₀) :
    WP isa (.block setupGP) s₀ fun s =>
      (∀ l < 2, s.lane .xmm0 l = revMask) ∧ (∀ l < 2, s.lane .xmm1 l = poly) ∧
      (∀ k < 8, ∀ l < 2, s.lane (preg16 k) l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 2 * k - l))) ∧
      (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  simp only [setupGP, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s₀ (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff, show ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] :
    List Instr) = [.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1)] ++ [.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] from rfl,
    WP.block_append_iff]
  refine WP.mono (vinsSelf_ok .xmm0 s₂) fun s₃ ⟨v₃, f₃⟩ => ?_
  refine WP.mono (vinsSelf_ok .xmm1 s₃) fun s₄ ⟨v₄, f₄⟩ => ?_
  have m0 : ∀ l < 2, s₄.lane .xmm0 l = revMask := fun l hl => by
    rw [f₄.lane _ (by decide) l hl, v₃ l hl]; show s₂.xmm .xmm0 = _; rw [o₂.xmm _ (by decide), c₁]; rfl
  have m1 : ∀ l < 2, s₄.lane .xmm1 l = poly := fun l hl => by
    rw [v₄ l hl, f₃.lane _ (by decide) 0 (by decide)]; exact c₂
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₄ m1) fun s₅ ⟨c8, c9, f₅⟩ => ?_
  have g₅ : ∀ r, r ≠ .rax → s₅.gpr r = s₀.gpr r := fun r hr => by rw [f₅.gpr, f₄.gpr, f₃.gpr, o₁₂.gpr r hr]
  have mm₅ : s₅.mem = s₀.mem := by rw [f₅.mem, f₄.mem, f₃.mem, o₁₂.mem]
  have rd₅ : s₅.rd = s₀.rd := by rw [f₅.rd, f₄.rd, f₃.rd, o₁₂.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [f₅.wr, f₄.wr, f₃.wr, o₁₂.wr]
  refine WP.mono (cvtRun_ok hp.toP 8 (Nat.le_refl _) s₅ (g₅ _ (by decide)) mm₅ rd₅ wr₅
    (fun l hl => by rw [f₅.lane _ (by decide) l hl]; exact m0 l hl) c8 c9) fun s' ⟨pw, F⟩ =>
    ⟨fun l hl => by rw [F.lane _ (by decide) l hl, f₅.lane _ (by decide) l hl]; exact m0 l hl,
      fun l hl => by rw [F.lane _ (by decide) l hl, f₅.lane _ (by decide) l hl]; exact m1 l hl, pw,
      fun r hr => by rw [F.gpr, g₅ r hr], by rw [F.mem, mm₅], by rw [F.rd, rd₅], by rw [F.wr, wr₅]⟩

/-- The setup: the state the loop starts from, with the powers
`Pₖₗ = H¹⁶⁻⁴ᵏ⁻ˡ · x⁻¹` in the working space. -/
theorem setupPTo_ok {s₀ : State} (hp : SPreTo CtxMode.powers s₀) :
    WP isa (.block setupP) s₀ fun s => ∃ P, ReadyTo s₀ P s ∧
      ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)) := by
  rw [setupP, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setupGPTo_ok hp) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  exact WP.mono (setupTTo_ok hp l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR => WP.mono (setupZTo_ok hR) fun _ hR' =>
    ⟨_, hR', fun k hk l hl => by
      rw [show 16 - 4 * k - l = 16 - 2 * (2 * k + l / 2) - l % 2 by omega_using []]
      exact pw _ (by omega_using [hk, hl]) _ (by omega_using [])⟩

/-- The out-of-place loop with the powers loaded meets its contract. -/
theorem stitchToP_ok : StitchToOkM CtxMode.powers Impl.Gcm.X86_64.StitchZTo.encP := fun s₀ hp hm =>
  WP.seq (WP.mono (setupPTo_ok hp) fun _ ⟨_, hR, hpw⟩ =>
    encTailGTo_ok hp hm (finZ (finP hpw))
      144 (by decide) (by decide) (fun _ h hI => bigPTo_ok hp (finZ (finP hpw)) hpw (fin48P (hk s₀)) (Nat.le_trans (by decide) h) hI) hR)

end VG.Proof.Gcm.X86_64.StitchZTo

/-! ## Prepared powers and cached AES keys -/

namespace VG.Proof.Gcm.X86_64.StitchZH
open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch (nb SPrePrepared StitchOkM CtxMode EPost DPost hk)
open VG.Proof.Gcm.X86_64.StitchZ (finZ)
open VG.Proof.Gcm.X86_64.StitchZP (finP fin48P)
open VG.Proof.Gcm.X86_64.Pclmul (Prod φ_reduceB)
open VG.Spec.Gcm (Block ghashFrom)

/-- What lane `n mod 4` gets of block `n`, added up over the four lanes. -/
theorem laneAccG_sum_succ (X : Nat → Block) (T : Nat → BitVec 128) (y : Block) (n : Nat) :
    (laneAccG X T y 0 (n + 1)).val + (laneAccG X T y 1 (n + 1)).val + (laneAccG X T y 2 (n + 1)).val +
        (laneAccG X T y 3 (n + 1)).val =
      (laneAccG X T y 0 n).val + (laneAccG X T y 1 n).val + (laneAccG X T y 2 n).val +
        (laneAccG X T y 3 n).val + x * φ ((if n = 0 then y else 0) ^^^ X n) * φ (T n) := by
  have hl : n % 4 < 4 := Nat.mod_lt _ (by decide)
  simp only [laneAccG]
  rcases (by omega_using [] : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h | h | h | h <;>
  simp only [h, ite_true, ite_false, show ¬ ((0 : Nat) = 1) by decide, show ¬ ((0 : Nat) = 2) by decide,
    show ¬ ((0 : Nat) = 3) by decide, show ¬ ((1 : Nat) = 0) by decide, show ¬ ((1 : Nat) = 2) by decide,
    show ¬ ((1 : Nat) = 3) by decide, show ¬ ((2 : Nat) = 0) by decide, show ¬ ((2 : Nat) = 1) by decide,
    show ¬ ((2 : Nat) = 3) by decide, show ¬ ((3 : Nat) = 0) by decide, show ¬ ((3 : Nat) = 1) by decide,
    show ¬ ((3 : Nat) = 2) by decide, Prod.val_acc] <;> ring

/-- The products of the `r` blocks after the last group with the powers
the setup stores, in the lanes of the masked group, add up to `GHASH` over
them. -/
theorem remZG {H : Block} {P : Nat → Nat → Block}
    (hP : ∀ k < 4, ∀ l < 4, x * φ (P k l) = φ H ^ (16 - 4 * k - l)) : RemOkG H P := by
  intro r hr1 hr15 X y
  let T : Nat → BitVec 128 := fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4)
  have hT : ∀ j < r, x * φ (T j) = φ H ^ (r - j) := fun j hj => by
    have := hP ((16 - r + j) / 4) (by omega_using [hr15, hj]) ((16 - r + j) % 4) (by omega_using [])
    rwa [show 16 - 4 * ((16 - r + j) / 4) - (16 - r + j) % 4 = r - j by omega_using [hr15]] at this
  have key : ∀ n, 1 ≤ n → n ≤ r →
      (laneAccG X T y 0 n).val + (laneAccG X T y 1 n).val + (laneAccG X T y 2 n).val +
          (laneAccG X T y 3 n).val = φ H ^ (r - n) * φ (ghashFrom H y ((List.range n).map X)) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ n ih =>
      intro _ hn
      rw [laneAccG_sum_succ]
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · have h0 := hT 0 (by omega_using [hr1])
        have hg : ghashFrom H y ((List.range (0 + 1)).map X) = Spec.Gcm.mul (y ^^^ X 0) H := rfl
        rw [hg, φ_mul]
        simp only [laneAccG, ↓reduceIte, Prod.val_zero]
        rw [show r - 0 = (r - (0 + 1)) + 1 by omega_using [hr1], pow_succ] at h0
        linear_combination φ (y ^^^ X 0) * h0
      · have hn' := hT n (by omega_using [hn])
        rw [show r - n = (r - (n + 1)) + 1 by omega_using [hn], pow_succ] at hn'
        rw [ih hpos (by omega_using [hn])]
        simp only [show n ≠ 0 by omega_using [hpos], ↓reduceIte, List.range_succ, List.map_append, List.map_cons,
          List.map_nil, ghashFrom, List.foldl_append, List.foldl_cons, List.foldl_nil, φ_mul, φ_xor, φ_zero,
          zero_add]
        rw [show r - n = (r - (n + 1)) + 1 by omega_using [hn], pow_succ]
        linear_combination φ (X n) * hn'
  apply φ_inj
  rw [φ_xor, φ_xor, φ_xor, φ_reduceB, φ_reduceB, φ_reduceB, φ_reduceB]
  have := key r hr1 (Nat.le_refl _)
  rw [Nat.sub_self, pow_zero, one_mul] at this
  rw [← this]
  ring

/-- `encR`, for any number of blocks from 16 on. -/
theorem encR_ok {s₀ : State} (hp : SPrePrepared s₀) :
    WP isa Impl.Gcm.X86_64.StitchZH.encR s₀ (EPost s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun s ⟨_, hR, hpw, hK⟩ =>
    StitchZC.midSel_ok s
      (fun _ _ _ f hh => midC_ok hp (remZG (finP hpw)) hpw (fin48P (hk s₀)) (ready_frame hR f)
        (hK.keep hh ((ready_frame hR f).a.keys hp.base)))
      (fun _ _ f hh => encTailRG_ok hp.base (finZ (finP hpw)) (remZG (finP hpw)) 144 (by decide) (by decide)
        (fun _ h hI hC => bigP_ok hp (finZ (finP hpw)) hpw (fin48P (hk s₀)) (Nat.le_trans (by decide) h) hI hC)
        (ready_frame hR f) (hK.keep hh ((ready_frame hR f).a.keys hp.base))))

/-- `decR`, for any number of blocks from 16 on. -/
theorem decR_ok {s₀ : State} (hp : SPrePrepared s₀) :
    WP isa Impl.Gcm.X86_64.StitchZH.decR s₀ (DPost s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨_, hR, hpw, hK⟩ =>
    decTailRG_ok hp.base (finZ (finP hpw)) (remZG (finP hpw))
      96 (by decide) (by decide) (fun _ h96 hI hC => bigDP_ok hp hpw (fin48P (hk s₀)) h96 hI hC) hR hK)

/-- Encryption and decryption of any number of blocks from 16 on. -/
theorem stitchR_ok :
    StitchOkM CtxMode.prepared Impl.Gcm.X86_64.StitchZH.encR Impl.Gcm.X86_64.StitchZH.decR 1 1 :=
  ⟨fun _ hp _ => encR_ok hp.toPrepared, fun _ hp _ => decR_ok hp.toPrepared⟩

end VG.Proof.Gcm.X86_64.StitchZH

namespace VG.Proof.Gcm.X86_64.StitchZHTo
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (nb StitchToOkM CtxMode hk)
open VG.Proof.Gcm.X86_64.StitchZ (finZ)
open VG.Proof.Gcm.X86_64.StitchZP (finP fin48P)

/-- `encR`, for any number of blocks from 16 on. -/
theorem encRTo_ok {s₀ : State} (hp : Proof.Gcm.X86_64.Stitch.SPreTo CtxMode.prepared s₀) :
    WP isa Impl.Gcm.X86_64.StitchZHTo.encR s₀ (Proof.Gcm.X86_64.Stitch.EPostTo s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun s ⟨_, hR, hpw, hK⟩ =>
    StitchZC.midSel_ok s
      (fun _ _ _ f hh => midCTo_ok hp (StitchZH.remZG (finP hpw)) hpw (fin48P (hk s₀)) (ready_frame hR f)
        (hK.keep hh ((ready_frame hR f).a.keys hp)))
      (fun _ _ f hh => encTailRGTo_ok hp (finZ (finP hpw)) (StitchZH.remZG (finP hpw)) 144 (by decide) (by decide)
        (fun _ h hI hC => bigPTo_ok hp (finZ (finP hpw)) hpw (fin48P (hk s₀)) (Nat.le_trans (by decide) h) hI hC)
        (ready_frame hR f) (hK.keep hh ((ready_frame hR f).a.keys hp))))

/-- Prepared powers and cached AES keys, out of place, for any number of
blocks from 16 on. -/
theorem stitchToR_ok : StitchToOkM CtxMode.prepared Impl.Gcm.X86_64.StitchZHTo.encR 1 :=
  fun _ hp _ => encRTo_ok hp

/-- What `encN`'s loops over `src` leave (`PhaseOne`), from the powers the
setup stores. -/
theorem phase1_ok : PhaseOne := fun {s₀} hp hm =>
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨P, hR, hpw, hK⟩ =>
    WP.mono (phase1G_ok hp hm (finZ (finP hpw)) 48 (by decide) (by decide)
      (fun _ _ hI hC => bigSTo_ok hp (finZ (finP hpw)) hpw (fin48P (hk s₀)) hI hC) hR hK)
      fun _ ⟨e, he, hI, hK'⟩ => ⟨P, e, he, hI, hK', finZ (finP hpw)⟩)

end VG.Proof.Gcm.X86_64.StitchZHTo

/-! ## The out-of-place loop on 256-bit registers (`Impl.Gcm.X86_64.StitchTo`)

The setup computes the
powers `H'`–`H'¹⁶` as `Stitch.setupG_ok` does (`StitchZTo.setupGTo_ok`) and
stores them (`StitchZTo.setupTTo_ok`); the loop then hashes with them
(`Stitch.finE`). The loop reads only the hash subkey from the key context,
so it meets the contract for a key context of any kind.
-/

namespace VG.Proof.Gcm.X86_64.StitchTo

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch (nb SPreTo StitchToOkM CtxMode hk finE)
open VG.Proof.Gcm.X86_64.StitchZTo (setupGTo_ok setupTTo_ok)
open VG.Impl.Gcm.X86_64.StitchTo (setup)
open VG.Spec.Gcm (Block)

/-- The setup: the state the loop starts from, with the powers
`x · Pₖₗ = H¹⁶⁻²ᵏ⁻ˡ` in the working space. -/
theorem setupTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) :
    WP isa (.block setup) s₀ fun s => ∃ P, ReadyTo s₀ P s ∧
      ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ (hk s₀) ^ (16 - 2 * k - l) := by
  rw [setup, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setupGTo_ok hp) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  exact WP.mono (setupTTo_ok hp l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR => ⟨_, ReadyTo.ofReady2 hR, pw⟩

/-- The out-of-place loop meets its contract, for a key context of any
kind. -/
theorem stitchTo_ok (M : CtxMode) : StitchToOkM M Impl.Gcm.X86_64.StitchTo.enc := fun _ hp hm =>
  WP.seq (WP.mono (setupTo_ok hp) fun _ ⟨_, hR, hpw⟩ => encTailTo_ok hp hm (finE hpw) hR)

end VG.Proof.Gcm.X86_64.StitchTo
