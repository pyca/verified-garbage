module

import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.OutOfPlace
import VerifiedGarbage.Proof.Gcm.Powers
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.RemE
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.SetupFin
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Reduction
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemSetup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.RemPairE
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemD
public import VerifiedGarbage.Proof.Gcm.Poly
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Cvt
public import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZHTo
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop48
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop48To
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZC.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Prepared
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZC
import VerifiedGarbage.Proof.Framework.X86_64.HighKeep
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop48
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop48
import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Ghash
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.OnePass
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.PhaseOne
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Group

/-! ### `Gcm.X86_64.StitchZ.OkP`, which the modules that import this one used -/

section

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

end

end

/-! ### `Gcm.X86_64.StitchR.RemETo`, which only this module used -/

section

/-!
# The out-of-place 256-bit encryption loop: the blocks after the last group

`encToR` is `StitchTo.enc` for any number of blocks from 16 on, as `encR`
is `enc` (`RemE.lean`). Once its loop stops with `r` blocks left
(`StitchTo.EInvTo`), `lastGRTo_ok` hashes the last group of the output, as
`StitchTo.finalTo_ok` does, and moves `rdx` to the output and `r8` to the
plaintext of the blocks after it (`EInvRTo`); `remETo_ok` then encrypts them
from the plaintext to the output, as `remE_ok` does in place, with
`StitchR.remE .r8`, the keystream computed on the in-place view `dst s₀`
(`SPreTo.toD`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchR

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo EPostTo CtxMode sp op sR oR FinOk ghRun_ok nb nr kp pp cp yp cb ciph
  sch hk y₀ dp dR pR cR yR addr_eq in_sub in_sub_int in_rdwr store16_ok ghash_append16 GEnv ghFin
  blockAt_writeW_sep')
open VG.Proof.Gcm.X86_64.StitchZTo (dst dst_gpr_ne dst_mem sAddr pblk ctbT oAddr blocks_ctr32To)
open VG.Proof.Gcm.X86_64.StitchTo (EInvTo ReadyTo AInvTo)
open VG.Impl.Gcm.X86_64.Stitch (aregs ordE lastG storeY)
open VG.Impl.Gcm.X86_64.StitchTo (firstTo bodyTo)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB toNat_ofNat_lt)
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Impl.Gcm.X86_64.StitchR (ks ksSel remE tailE encToR)
open VG.Proof.Gcm.X86_64.StitchZH (REnv RInv accR accR_congr remSetup_ok keys_of)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-- After the last group of the output is hashed: `rdx` at the output and
`r8` at the plaintext of the `r` blocks after it, `r9 = 16 + r`. -/
structure EInvRTo (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  le : 16 * e ≤ nb s₀
  ctr : ∀ l < 2, s.lane .xmm14 l = Nat.repeat inc32 (16 * e + l) (cb s₀)
  msk : ∀ l < 2, s.lane .xmm0 l = revMask
  inc : ∀ l < 2, s.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  frame : Frame [oR s₀, pR s₀] s₀.mem s.mem
  blocks : ∀ k < 16 * e, blockAt s.mem (oAddr s₀ k) = ctbT s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rdx : s.gpr .rdx = op s₀ + BitVec.ofNat 64 (256 * e)
  r8 : s.gpr .r8 = sp s₀ + BitVec.ofNat 64 (256 * e)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (16 + (nb s₀ - 16 * e))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (ctbT s₀))
  y1 : s.lane .xmm2 1 = 0

/-- `add rdx, 256` and `add r8, rdx`. -/
theorem addRdxR8_ok (t : State) :
    WP isa (.block [.alu .add .rdx (.imm 256), .alu .add .r8 (.reg .rdx)]) t fun t' =>
      t'.gpr .rdx = t.gpr .rdx + BitVec.ofNat 64 256 ∧ t'.gpr .r8 = t.gpr .r8 + (t.gpr .rdx + BitVec.ofNat 64 256) ∧
      (∀ q, q ≠ .rdx → q ≠ .r8 → t'.gpr q = t.gpr q) ∧
      (∀ x l, t'.lane x l = t.lane x l) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain e256 : BitVec.signExtend 64 (256 : BitVec 32) = BitVec.ofNat 64 256 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
    State.setFlags, isa, State.setReg, e256, reduceCtorEq, ↓reduceIte,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun q h1 h2 => by simp only [h1, h2, ↓reduceIte], fun _ _ => rfl, trivial, trivial,
    trivial⟩

/-- The last group of the output hashed, as `StitchTo.finalTo_ok` does without
the stores, `rdx` moved to the output and `r8` to the plaintext of the blocks
after it. -/
theorem lastGRTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block}
    (hf : FinOk ordE (hk s₀) P) {e : Nat} (hgt : 16 * e < nb s₀) {s : State} (hI : EInvTo s₀ P e s) :
    WP isa (.block ((lastG ++ ([.alu .add .rdx (.imm 256)] : List Instr)) ++
      ([.alu .add .r8 (.reg .rdx)] : List Instr))) s (EInvRTo s₀ P e) := by
  have hw := hp.wrap_o
  have h1e := hI.one
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctbT s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.lane .xmm2 l
  have ha : a.toNat = (op s₀).toNat + 256 * (e - 1) := hI.rdx
  obtain hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [List.append_assoc, show ([.alu .add .rdx (.imm 256)] : List Instr) ++ [.alu .add .r8 (.reg .rdx)] =
    [.alu .add .rdx (.imm 256), .alu .add .r8 (.reg .rdx)] from rfl]
  simp only [lastG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_lanes s) fun s₂ ⟨z₂, f₂, _⟩ => ?_
  obtain hE₂ : GEnv (dst s₀) 0 a X P s₂ :=
    { rdx := by rw [f₂.gpr]
      r11 := by rw [f₂.gpr]; exact hr11
      xs := fun i _ hi => by
        rw [f₂.mem, show a + BitVec.ofNat 64 (16 * i) = oAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega_arith),
          hI.a.blocks _ (by omega_arith)]
      pv := fun k hk l hl => by rw [f₂.mem]; exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₂.rd, f₂.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (32 * k) = op s₀ + BitVec.ofNat 64 (256 * (e - 1) + 32 * k) from
            addr_eq (by omega_arith)]
        exact in_rdwr (in_sub hp.o_in (by omega_arith))
      inp := fun k hk => by
        rw [f₂.rd, f₂.wr, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega_arith))
      m0 := fun l hl => by rw [f₂.lane _ (by decide) l hl]; exact hI.a.msk l hl }
  rw [WP.block_append_iff]
  refine WP.mono (ghRun_ok (yl := yl) 8 (Nat.le_refl _) s₂ hE₂ z₂
    (fun l hl => by rw [f₂.lane _ (by decide) l hl])) fun s₃ ⟨hE₃, p₃, _, f₃⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (ghFin hE₃ (fun l hl => by
      rw [f₃.lane _ (by decide) l hl, f₂.lane _ (by decide) l hl]; exact hI.m1 l hl))
    fun s₄ ⟨_, y4, y41, f₄⟩ => ?_
  rw [p₃ 0 (by decide), p₃ 1 (by decide)] at y4
  obtain F : YFrame (([.xmm8, .xmm9, .xmm10] : List XReg) ++
      (([.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] : List XReg) ++
      ([.xmm8, .xmm9, .xmm10, .xmm11, .xmm7, .xmm11, .xmm2] : List XReg))) s s₄ := f₂.comp (f₃.comp f₄)
  obtain hA₄ : AInvTo s₀ (16 * e) s₄ := hI.a.yframe F (by decide) (by decide) (by decide)
  refine WP.mono (addRdxR8_ok s₄) fun s₅ ⟨d₅, r8₅, g₅, l₅, m₅, rd₅, wr₅⟩ => ?_
  obtain gk : ∀ q, q ≠ .rdx → q ≠ .r8 → s₅.gpr q = s.gpr q := fun q h1 h2 => by rw [g₅ q h1 h2, F.gpr]
  obtain hm : s₅.mem = s.mem := by rw [m₅, F.mem]
  obtain hd : s.gpr .rdx + BitVec.ofNat 64 256 = op s₀ + BitVec.ofNat 64 (256 * e) := by
    apply BitVec.eq_of_toNat_eq
    obtain hd := (op s₀).isLt
    rw [BitVec.toNat_add, BitVec.toNat_add, show (s.gpr .rdx).toNat = _ from ha, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 256 < 2 ^ 64 by decide),
      Nat.mod_eq_of_lt (show 256 * e < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  refine
    { le := hA₄.le
      ctr := fun l hl => by rw [l₅]; exact hA₄.ctr l hl
      msk := fun l hl => by rw [l₅]; exact hA₄.msk l hl
      inc := fun l hl => by rw [l₅]; exact hA₄.inc l hl
      rdi := by rw [g₅ _ (by decide) (by decide)]; exact hA₄.rdi
      rsi := by rw [g₅ _ (by decide) (by decide)]; exact hA₄.rsi
      frame := by rw [m₅]; exact hA₄.frame
      blocks := fun k hk => by rw [m₅]; exact hA₄.blocks k hk
      rd := by rw [rd₅]; exact hA₄.rd
      wr := by rw [wr₅]; exact hA₄.wr
      rdx := by rw [d₅, F.gpr, hd]
      r8 := by
        rw [r8₅, F.gpr, hd, hI.a.r8, ← BitVec.add_assoc, BitVec.sub_add_cancel]
      r9 := by
        rw [gk _ (by decide) (by decide), hI.r9]
        congr 1; have := hI.a.le; omega_arith
      rax := by rw [gk _ (by decide) (by decide)]; exact hI.rax
      gpr := fun q h1 h2 h3 h4 h5 => by rw [gk q h2 h3]; exact hI.gpr q h1 h2 h3 h4 h5
      pw := fun k hk l hl => by rw [hm]; exact hI.pw k hk l hl
      m1 := fun l hl => by rw [l₅, F.lane _ (by decide) l hl]; exact hI.m1 l hl
      y := by
        rw [l₅, y4]
        refine (hf X yl hI.y1).trans ?_
        rw [show 16 * e = 16 * ((e - 1) + 1) by congr 1; omega_arith, ghash_append16]
        exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y
      y1 := by rw [l₅]; exact y41 }

theorem remETo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (hc : CtxPow s₀ (oR s₀))
    (hr : RemLaw (hk s₀) (powC s₀)) {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : EInvRTo s₀ P e s) (hlt : nb s₀ - 16 * e < 16) (hne : nb s₀ ≠ 16 * e) :
    WP isa (remE .r8) s (EPostTo s₀) := by
  have hd := hp.toD
  have hw := hp.wrap_o
  have hws := hp.wrap_s
  have hwp := hp.wrap_p
  have hle := hI.le
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  obtain epp : pp (dst s₀) = pp s₀ := dst_gpr_ne s₀ (by decide)
  obtain eci : ciph (dst s₀) = ciph s₀ := by
    simp only [ciph, sch, nr, kp, dst_mem, dst_gpr_ne s₀ (show Reg.rdi ≠ .r8 by decide),
      dst_gpr_ne s₀ (show Reg.rsi ≠ .r8 by decide)]
  obtain ecb : cb (dst s₀) = cb s₀ := by
    simp only [cb, cp, dst_mem, dst_gpr_ne s₀ (show Reg.rdx ≠ .r8 by decide)]
  obtain ⟨r, hr_def⟩ : ∃ r, r = nb s₀ - 16 * e := ⟨_, rfl⟩
  obtain hr1 : 1 ≤ r := by omega_arith
  obtain hr15 : r ≤ 15 := by omega_arith
  obtain hr9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r) := by rw [hI.r9, ← hr_def]
  obtain hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [show remE .r8 = .seq (.block Impl.Gcm.X86_64.StitchR.remSetupC) (.seq ksSel
      (.seq (.block ((([.alu .sub .r11 (.imm 512), .mov32 .r10 (.imm 0)] : List Instr) ++
          Impl.Gcm.X86_64.StitchAvx.zero) ++ ([.alu .test .r9 (.imm 1)] : List Instr)))
        (.seq (.ite .e (.block [.alu .cmp .r9 (.imm 16)])
            (.block (Impl.Gcm.X86_64.StitchR.remOneC .r8)))
          (.seq (.ite .e (.block []) (.seq (.loop (.block (Impl.Gcm.X86_64.StitchR.remPairE .r8 ++
              [.alu .sub .rax (.imm 64)] ++ Impl.Gcm.X86_64.StitchR.remNextPair)) .ne)
              (.block Impl.Gcm.X86_64.StitchR.foldLanes)))
            (.seq (.block (Impl.Gcm.X86_64.StitchAvx.reduceHash ++ ([.alu .add .r11 (.imm 512)] : List Instr)))
              (.seq Impl.Gcm.X86_64.StitchR.zeroKs (.block storeY))))))) from rfl]
  -- The counter after all the blocks, and `rax` at the powers of the `r` blocks in the key context.
  refine WP.seq (WP.mono (remSetupC_ok s hr1 hr15 hr9 (hI.msk 0 (by decide))
    (by rw [hI.rax, hI.wr]; exact in_sub_int hp.c_in (by omega_arith)))
    fun s₁ ⟨m₁, a10₁, ax₁, g₁, rd₁, wr₁, z₁⟩ => ?_)
  obtain e0 : cp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int) = cp s₀ := by
    rw [BitVec.ofInt_natCast]; exact BitVec.add_zero _
  rw [hI.rax, e0] at m₁
  rw [hI.rdi] at ax₁
  obtain lk₁ : ∀ x, x ≠ .xmm13 → ∀ l < 2, s₁.lane x l = s.lane x l := fun x h l hl => by
    rw [← State.zlane_lt2 _ _ hl, z₁ x h l (by omega_arith), State.zlane_lt2 _ _ hl]
  obtain cw : (cR s₀).Contains (cp s₀) (128 / 8) := Region.contains_self _ _
  obtain hfr₁ : Frame [oR s₀, pR s₀, cR s₀] s₀.mem s₁.mem := by
    rw [m₁]
    exact (hI.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _ cw
  obtain hrd₁ : s₁.rd = s₀.rd := by rw [rd₁]; exact hI.rd
  obtain hwr₁ : s₁.wr = s₀.wr := by rw [wr₁]; exact hI.wr
  obtain hrdi₁ : s₁.gpr .rdi = kp s₀ := by rw [g₁ _ (by decide) (by decide)]; exact hI.rdi
  -- The keystream, on the in-place view.
  refine WP.seq (WP.mono (ksSel_ok hd hr1 hr15 (c := 16 * e) a10₁
    (fun l hl => by rw [lk₁ _ (by decide) l hl, ecb]; exact hI.ctr l hl)
    (fun l hl => by rw [lk₁ _ (by decide) l hl]; exact hI.msk l hl)
    (fun l hl => by rw [lk₁ _ (by decide) l hl]; exact hI.inc l hl)
    (keys_of hd hrdi₁ hrd₁ hwr₁ hfr₁)
    (by rw [g₁ _ (by decide) (by decide), dst_gpr_ne s₀ (by decide)]; exact hI.rsi) hrdi₁
    (by rw [g₁ _ (by decide) (by decide), epp]; exact hr11) hwr₁)
    fun s₂ ⟨ks₂, g₂, rd₂, wr₂, l₂, f₂⟩ => ?_)
  rw [epp] at ks₂ f₂
  -- `r11` lowered, `r10 = 0`, the products cleared.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (preV_ok s₂) fun s₃ ⟨d₃, z₃, g₃, p₃, l₃, m₃, rd₃, wr₃⟩ => ?_
  obtain gk₃ : ∀ q, q ≠ .r10 → q ≠ .r11 → q ≠ .rax → s₃.gpr q = s.gpr q := fun q h1 h11 h2 => by
    rw [g₃ q h11 h1, g₂ q h1, g₁ q h1 h2]
  obtain lk₃ : ∀ x, x ≠ .xmm8 → x ≠ .xmm9 → x ≠ .xmm10 → x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs →
      ∀ l < 2, s₃.lane x l = s.lane x l := fun x h8 h9 h10 h13 h14 ha l hl => by
    rw [← State.zlane_lt2 _ _ hl, l₃ x h8 h9 h10 l (by omega_arith), State.zlane_lt2 _ _ hl, l₂ x h13 h14 ha l hl,
      lk₁ x h13 l hl]
  obtain h11₃ : s₃.gpr .r11 = pp s₀ - BitVec.ofNat 64 512 := by
    rw [d₃, g₂ _ (by decide), g₁ _ (by decide) (by decide), hr11]
  obtain eK : ∀ j, pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j) =
      pp s₀ + BitVec.ofNat 64 (256 + 16 * j) := fun j => by
    rw [show 768 + 16 * j = 512 + (256 + 16 * j) by omega_arith, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
      BitVec.sub_add_cancel]
  obtain hA : s₃.gpr .rdx = oAddr s₀ (16 * e) := by
    rw [gk₃ _ (by decide) (by decide) (by decide), hI.rdx]
    show op s₀ + BitVec.ofNat 64 (256 * e) = op s₀ + BitVec.ofNat 64 (16 * (16 * e))
    rw [show 256 * e = 16 * (16 * e) by omega_arith]
  obtain hS : s₃.gpr .r8 = sAddr s₀ (16 * e) := by
    rw [gk₃ _ (by decide) (by decide) (by decide), hI.r8]
    show sp s₀ + BitVec.ofNat 64 (256 * e) = sp s₀ + BitVec.ofNat 64 (16 * (16 * e))
    rw [show 256 * e = 16 * (16 * e) by omega_arith]
  let E : REnv := REnv.mk r .r8 (sAddr s₀ (16 * e)) (oAddr s₀ (16 * e)) (pp s₀ - BitVec.ofNat 64 512)
    (kp s₀ + BitVec.ofNat 64 224) s₃.mem s₃.gpr s₃.rd s₃.wr (s₃.lane .xmm2 0)
  have hwk := hc.wrap_k
  obtain eC : ∀ j, j < r → E.aC j = kp s₀ + BitVec.ofNat 64 (224 + 16 * (r - j) + 32 * ((r - j) % 2)) := fun j _ => by
    show kp s₀ + BitVec.ofNat 64 224 + BitVec.ofNat 64 (16 * (r - j) + 32 * ((r - j) % 2)) = _
    rw [Offset.add_add, Nat.add_assoc]
  obtain kD : ∀ {d n : Nat}, d + n ≤ 512 → Region.Disjoint ⟨kp s₀ + BitVec.ofNat 64 d, n⟩ ⟨oAddr s₀ (16 * e), 16 * r⟩ :=
    fun {d n} h => (hc.d_k.symm.sub_left (Offset.sub_base _ h)).sub_right
      (Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith))
  obtain hrd₃ : s₃.rd = s₀.rd := by rw [rd₃, rd₂, hrd₁]
  obtain hwr₃ : s₃.wr = s₀.wr := by rw [wr₃, wr₂, hwr₁]
  obtain hE : OkC E :=
    { r1 := hr1, r15 := hr15, gS := hS, gA := hA, gP := h11₃
      gW := by
        show s₃.gpr .rax = _; rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), ax₁]
      src9 := by show Reg.r8 ≠ Reg.r9; decide, src10 := by show Reg.r8 ≠ Reg.r10; decide
      srcA := by show Reg.r8 ≠ Reg.rax; decide
      inS := fun j (hj : j < r) => by
        show InRegions (s₃.rd ++ s₃.wr) (sAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 16
        rw [hrd₃, hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_sub hp.s_in (by omega_arith)
      inK := fun j (hj : j < r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j)) 16
        rw [hrd₃, hwr₃, eK]
        exact in_rdwr (in_sub hp.p_in (by omega_arith))
      inD := fun j (hj : j < r) => by
        show InRegions s₃.wr (oAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 16
        rw [hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_sub hp.o_in (by omega_arith)
      inW := fun j (hj : j < r) => by
        rw [eC j hj, show E.rd ++ E.wr = s₃.rd ++ s₃.wr from rfl, hrd₃, hwr₃]
        exact in_sub hc.k_in (by omega_arith)
      dS := fun j (hj : j < r) i hi => by
        show Region.Disjoint ⟨sAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j), 16⟩ ⟨oAddr s₀ (16 * e), 16 * i⟩
        rw [Offset.add_add]
        exact (hp.s_o.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
      dK := fun j (hj : j < r) => by
        show Region.Disjoint ⟨pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j), 16⟩
          ⟨oAddr s₀ (16 * e), 16 * r⟩
        rw [eK]
        exact (hp.o_p.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
      dW := fun j (hj : j < r) => by
        rw [eC j hj]; exact kD (by omega_arith)
      inS2 := fun j (hj : j + 2 ≤ r) => by
        show InRegions (s₃.rd ++ s₃.wr) (sAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 32
        rw [hrd₃, hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_sub hp.s_in (by omega_arith)
      inK2 := fun j (hj : j + 2 ≤ r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j)) 32
        rw [hrd₃, hwr₃, eK]
        exact in_rdwr (in_sub hp.p_in (by omega_arith))
      inD2 := fun j (hj : j + 2 ≤ r) => by
        show InRegions s₃.wr (oAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 32
        rw [hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_sub hp.o_in (by omega_arith)
      inW2 := fun j (hj : j + 2 ≤ r) (hev : (r - j) % 2 = 0) => by
        rw [eC j (by omega_arith), show E.rd ++ E.wr = s₃.rd ++ s₃.wr from rfl, hrd₃, hwr₃]
        exact in_sub hc.k_in (by omega_arith) }
  obtain hI₃ : RInvC E E.X 0 s₃ :=
    { le := Nat.zero_le _, r10 := z₃
      ax := by
        show s₃.gpr .rax + s₃.gpr .r10 = kp s₀ + BitVec.ofNat 64 224 + BitVec.ofNat 64 (16 * (r - 0))
        rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), ax₁, z₃, Nat.sub_zero]
        exact BitVec.add_zero _
      r9 := by
        show s₃.gpr .r9 = _
        rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), g₁ _ (by decide) (by decide), hr9, Nat.sub_zero]
      gpr := fun _ _ _ _ => rfl, rd := rfl, wr := rfl
      frame := Frame.refl _ _
      ct := fun j hj => absurd hj (Nat.not_lt_zero _)
      prod := by
        obtain ⟨a, b, c⟩ := p₃ 0 (by decide)
        simp only [prod, State.proj_xmm, ← State.zlane_lt2 _ _ (show 0 < 2 by decide), a, b, c]
        rfl
      y := rfl
      m0 := by
        rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0 (by decide)]
        exact hI.msk 0 (by decide)
      m1 := by
        rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0 (by decide)]
        exact hI.m1 0 (by decide) }
  obtain z1 : ∀ x, s₃.zlane x 1 = 0 → s₃.lane x 1 = 0 := fun x h => by rw [← State.zlane_lt2 _ _ (by decide)]; exact h
  -- The first block alone if `r` is odd, then the pairs and their lanes added.
  refine remMidC_ok (E := E) hE hI₃ (z1 _ (p₃ 1 (by decide)).1) (z1 _ (p₃ 1 (by decide)).2.1)
    (z1 _ (p₃ 1 (by decide)).2.2)
    (by rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 1 (by decide)]; exact hI.y1)
    (by rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 1 (by decide)]
        exact hI.msk 1 (by decide)) fun s₄ hI₄ => ?_
  -- The products reduced into `Y`, `r11` restored, the keystream cleared, and `Y` stored.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (StitchAvx.reduceHash_ok s₄ hI₄.m1) fun s₅ ⟨y₅, f₅⟩ => ?_
  refine WP.mono (add11_ok s₅) fun s₅a ⟨a11, g₅a, l₅a, m₅a, rd₅a, wr₅a⟩ => ?_
  obtain h11₅a : s₅a.gpr .r11 = pp s₀ := by
    rw [a11, f₅.gpr, hI₄.gpr _ (by decide) (by decide) (by decide)]
    show s₃.gpr .r11 + BitVec.ofNat 64 512 = _
    rw [h11₃, BitVec.sub_add_cancel]
  obtain h10₅a : s₅a.gpr .r10 = BitVec.ofNat 64 (16 * r) := by
    rw [g₅a _ (by decide), f₅.gpr, hI₄.r10]
  refine WP.seq (WP.mono (zeroKs_ok (r := r) hr15 h10₅a
    (by rw [h11₅a, wr₅a, f₅.wr, hI₄.wr]; show InRegions s₃.wr _ _; rw [hwr₃]; exact hp.p_in)
    (by rw [h11₅a]; exact hwp)) fun s₆ ⟨fz, zz, gz, rdz, wrz, lz⟩ => ?_)
  rw [h11₅a] at fz zz
  obtain g₆ : ∀ q, q ≠ .r11 → s₆.gpr q = s₅.gpr q := fun q h => by rw [gz, g₅a q h]
  obtain l₆ : ∀ x, x ≠ .xmm12 → ∀ l < 2, s₆.lane x l = s₅.lane x l := fun x h l hl => by rw [lz x h l hl, l₅a]
  obtain rd₆ : s₆.rd = s₅.rd := by rw [rdz, rd₅a]
  obtain wr₆ : s₆.wr = s₅.wr := by rw [wrz, wr₅a]
  obtain a11' : s₆.gpr .r11 = pp s₀ := by rw [gz, h11₅a]
  obtain hrcx : s₆.gpr .rcx = yp s₀ := by
    rw [g₆ _ (by decide), f₅.gpr, hI₄.gpr _ (by decide) (by decide) (by decide)]
    show s₃.gpr .rcx = _
    rw [gk₃ _ (by decide) (by decide) (by decide)]
    exact hI.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain m06 : s₆.lane .xmm0 0 = revMask := by
    rw [l₆ _ (by decide) 0 (by decide), f₅.lane _ (by decide) 0 (by decide)]; exact hI₄.m0
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl, WP.block_append_iff]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s₆ m06
    (by rw [hrcx, wr₆, f₅.wr, hI₄.wr]; show InRegions s₃.wr _ _; rw [hwr₃]; exact hp.y_in))
    fun s₇ ⟨m₇, g₇, rd₇, wr₇, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [hrcx, l₆ _ (by decide) 0 (by decide), y₅] at m₇
  obtain hm₅a : s₅a.mem = s₄.mem := by rw [m₅a, f₅.mem]
  rw [hm₅a] at fz
  obtain hnb : nb s₀ = 16 * e + r := by omega_arith
  -- What the stages keep of the memory before them.
  obtain toS : ∀ p : Addr, Region.Disjoint ⟨p, 16⟩ (cR s₀) →
      Region.Disjoint ⟨p, 16⟩ ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩ →
      blockAt s₃.mem p = blockAt s.mem p := fun p hc hk => by
    rw [m₃, blockAt_frame f₂ (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hk), m₁,
      show cp s₀ = (cR s₀).base from rfl, blockAt_writeW_sep' hc rfl]
  obtain oK : ∀ k, k < nb s₀ → Region.Disjoint ⟨oAddr s₀ k, 16⟩ ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩ := fun k hk =>
    (hp.o_p.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
  obtain oC : ∀ k, k < nb s₀ → Region.Disjoint ⟨oAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.o_c.sub_left (Offset.sub_base _ (by omega_arith))
  obtain hS' : ∀ j < r, blockAt s₃.mem (sAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) = pblk s₀ (16 * e + j) :=
    fun j hj => by
      obtain hk : 16 * e + j < nb s₀ := by omega_arith
      rw [Offset.add_add, ← Nat.mul_add,
        toS _ (hp.s_c.sub_left (Offset.sub_base _ (by omega_arith)))
          ((hp.s_p.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith)))]
      exact blockAt_frame hI.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.s_o.sub_left (Offset.sub_base _ (by omega_arith))
        · exact hp.s_p.sub_left (Offset.sub_base _ (by omega_arith))
  -- The ciphertext of the blocks after the last group.
  obtain hX : ∀ j < r, E.X j = ctbT s₀ (16 * e + j) := fun j hj => by
    show blockAt s₃.mem (sAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) ^^^
      blockAt s₃.mem (pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j)) = _
    rw [hS' j hj, eK, m₃, ks₂ j hj, eci, ecb]
  -- The blocks.
  obtain hb₄ : ∀ k < nb s₀, blockAt s₄.mem (oAddr s₀ k) = ctbT s₀ k := by
    intro k hk
    by_cases hke : k < 16 * e
    · rw [blockAt_frame hI₄.frame (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          show Region.Disjoint _ ⟨oAddr s₀ (16 * e), 16 * r⟩
          exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)),
        toS _ (oC k hk) (oK k hk), hI.blocks k hke]
    · obtain ⟨j, rfl⟩ : ∃ j, k = 16 * e + j := ⟨k - 16 * e, by omega_arith⟩
      obtain hj : j < r := by omega_arith
      obtain ct := hI₄.ct j hj
      obtain eD : E.aD j = oAddr s₀ (16 * e + j) := by
        show oAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j) = _
        rw [Offset.add_add, ← Nat.mul_add]
      rw [eD] at ct
      rw [ct, hX j hj]
  -- The powers, as the key context holds them: kept by the stores before the loop.
  obtain kS : ∀ {d : Nat}, d + 16 ≤ 512 →
      s₃.mem.readW (kp s₀ + BitVec.ofNat 64 d) 128 = s₀.mem.readW (kp s₀ + BitVec.ofNat 64 d) 128 := fun {d} hd => by
    obtain hsub : Region.Sub ⟨kp s₀ + BitVec.ofNat 64 d, 16⟩ ⟨kp s₀, 512⟩ := Offset.sub_base _ hd
    rw [m₃, f₂.readW (r := ⟨kp s₀ + BitVec.ofNat 64 d, 16⟩) (Region.contains_self _ _) (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact (hc.p_k.symm.sub_left hsub).sub_right (Offset.sub_base _ (by omega_arith))) (by decide),
      m₁, Mem.readW_writeW_sep ((hc.c_k.symm.sub_left hsub).sep (Region.contains_self _ _) cw) (by decide)]
    exact hI.frame.readW (r := ⟨kp s₀ + BitVec.ofNat 64 d, 16⟩) (Region.contains_self _ _) (fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact hc.d_k.symm.sub_left hsub
      · exact hc.p_k.symm.sub_left hsub) (by decide)
  obtain hT : ∀ j < r, E.TC j = powC s₀ ((16 - r + j) / 2) ((16 - r + j) % 2) := fun j hj => by
    show s₃.mem.readW (E.aC j) 128 = _
    rw [eC j hj, kS (by omega_arith), ctxPow_at hc (by omega_arith) (by omega_arith)]
    simp only [powC]
    congr 2; omega_arith
  obtain yO : ∀ k < nb s₀, Region.Disjoint ⟨oAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.o_y.sub_left (Offset.sub_base _ (by omega_arith))
  obtain hb : ∀ k < nb s₀, blockAt s₇.mem (oAddr s₀ k) = ctbT s₀ k := fun k hk => by
    rw [m₇, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' (yO k hk) rfl, blockAt_frame fz (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact oK k hk), hb₄ k hk]
  obtain fA : ∀ R : Region, R.Disjoint (oR s₀) → ∀ r' ∈ [(⟨E.A, 16 * E.r⟩ : Region)], R.Disjoint r' :=
    fun R hR r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hR.sub_right (Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith))
  obtain hy₃ : s₃.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (ctbT s₀)) := by
    rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0 (by decide)]
    exact hI.y
  refine ⟨blocks_ctr32To hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show blockAt s₇.mem (cp s₀) = _
    rw [m₇, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' hp.c_y rfl, blockAt_frame fz (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hp.p_c.symm.sub_right (Offset.sub_base _ (by omega_arith))),
      blockAt_frame hI₄.frame (fA _ hp.o_c.symm), show E.m = s₃.mem from rfl, m₃,
      blockAt_frame f₂ (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hp.p_c.symm.sub_right (Offset.sub_base _ (by omega_arith))),
      m₁, VG.Proof.Gcm.X86_64.blockAt_store, hI.ctr 0 (by decide), Nat.add_zero,
      VG.Proof.Aes.X86_64.AesNi.rep_add, hnb]
  · show blockAt s₇.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₇.mem (op s₀) (nb s₀))
    obtain hbl : blocksAt s₇.mem (op s₀) (nb s₀) = (List.range (nb s₀)).map (ctbT s₀) := by
      simp only [blocksAt]
      exact List.map_congr_left fun k hk => hb k (by simpa using hk)
    rw [hbl, m₇, VG.Proof.Gcm.X86_64.blockAt_store, hI₄.prod, accR_congr _ r hX hT, hr r hr1 hr15,
      show E.y = s₃.lane .xmm2 0 from rfl, hy₃, hnb, List.range_add, List.map_append, List.map_map]
    simp only [ghashFrom, List.foldl_append]
    rfl
  · show Frame _ s₀.mem s₇.mem
    obtain F0 : Frame [cR s₀, yR s₀, oR s₀, pR s₀] s₀.mem s.mem := hI.frame.sub fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    obtain F1 : Frame [cR s₀, yR s₀, oR s₀, pR s₀] s.mem s₁.mem := by
      rw [m₁]; exact (Frame.refl _ _).writeW (by simp) _ cw
    obtain F2 : Frame [cR s₀, yR s₀, oR s₀, pR s₀] s₁.mem s₃.mem := by
      rw [m₃]
      exact f₂.sub fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact ⟨pR s₀, by simp, Offset.sub_base _ (by omega_arith)⟩
    obtain F3 : Frame [cR s₀, yR s₀, oR s₀, pR s₀] s₃.mem s₄.mem := hI₄.frame.sub fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨oR s₀, by simp, Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith)⟩
    obtain F4 : Frame [cR s₀, yR s₀, oR s₀, pR s₀] s₄.mem s₆.mem := fz.sub fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨pR s₀, by simp, Offset.sub_base _ (by omega_arith)⟩
    rw [m₇]
    exact ((((F0.trans F1).trans F2).trans F3).trans F4).writeW (by simp) _ (Region.contains_self _ _)
  · intro q h1 h2 h3 h4 h5
    show s₇.gpr q = _
    by_cases h11 : q = .r11
    · subst h11
      rw [g₇, a11']
    · rw [g₇, g₆ q h11, f₅.gpr, hI₄.gpr q h4 h5 h1]
      show s₃.gpr q = _
      rw [gk₃ q h5 h11 h1]
      exact hI.gpr q h1 h2 h3 h4 h5
  · show s₇.rd = _
    rw [rd₇, rd₆, f₅.rd, hI₄.rd]; exact hrd₃
  · show s₇.wr = _
    rw [wr₇, wr₆, f₅.wr, hI₄.wr]; exact hwr₃

/-- The out-of-place loop, for any number of blocks from 16 on: it stops with
`16 + r` blocks left, `r < 16`. -/
theorem loopERTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block}
    (hf : FinOk ordE (hk s₀) P) {s : State}
    (hI : EInvTo s₀ P 1 s) (hcf : s.cf = some (decide (nb s₀ - 16 * (1 - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop bodyTo .ae)) s fun s' =>
      ∃ e, nb s₀ - 16 * (e - 1) < 32 ∧ EInvTo s₀ P e s' := by
  refine WP.ite (decide (nb s₀ - 16 * (1 - 1) < 32)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil ⟨1, by simpa using h, hI⟩
  · let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ EInvTo s₀ P e s
    obtain hstep : ∀ m s, I m s → WP isa bodyTo s (fun s' =>
        (eval .ae s' = some false ∧ ∃ e, nb s₀ - 16 * (e - 1) < 32 ∧ EInvTo s₀ P e s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨e, rfl, he, hI⟩
      refine WP.mono (StitchTo.bodyTo_ok hp hf he hI) fun s' ⟨hI', hcf'⟩ => ?_
      by_cases hlt : nb s₀ - 16 * e < 32
      · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
          e + 1, by simpa using hlt, hI'⟩
      · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
          nb s₀ - 16 * (e + 1), by have := hI.one; omega_arith, e + 1, rfl, by omega_arith, hI'⟩
    have := hI.a.le
    exact WP.loop (M := isa) I hstep (nb s₀ - 16 * 1) s ⟨1, rfl, by simp at h; omega_arith, hI⟩

/-- `cmp r9, 16` after the out-of-place loop. -/
theorem cmpE16To_ok {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : EInvTo s₀ P e s)
    (hlt : nb s₀ - 16 * (e - 1) < 32) :
    WP isa (.block [.alu .cmp .r9 (.imm 16)]) s fun s' =>
      EInvTo s₀ P e s' ∧ s'.zf = some (decide (nb s₀ = 16 * e)) := by
  have h1 := hI.one
  have hle := hI.a.le
  refine WP.mono (cmp916_ok s) fun s' ⟨z, g, l, m, rd, wr⟩ => ⟨?_, ?_⟩
  · have yf : YFrame [] s s' := ⟨g, m, rd, wr, fun x _ l' _ => l x l'⟩
    exact ⟨hI.a.yframe yf (by simp) (by simp) (by simp), hI.one, by rw [g]; exact hI.rdx, by rw [g]; exact hI.r9,
      by rw [g]; exact hI.rax, fun r h1 h2 h3 h4 h5 => by rw [g]; exact hI.gpr r h1 h2 h3 h4 h5,
      fun k hk l' hl => by rw [m]; exact hI.pw k hk l' hl, fun l' hl => by rw [l]; exact hI.m1 l' hl,
      by rw [l]; exact hI.y, by rw [l]; exact hI.y1⟩
  · rw [z, hI.r9, show nb s₀ - 16 * (e - 1) = 16 + (nb s₀ - 16 * e) by omega_arith, zero16 _ (by omega_arith)]
    congr 1
    exact decide_eq_decide.mpr ⟨fun h => by omega_arith, fun h => by omega_arith⟩

/-- `tailE`, out of place, once the loop has stopped. -/
theorem tailERTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (hc : CtxPow s₀ (oR s₀))
    {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) (hr : RemLaw (hk s₀) (powC s₀)) {e : Nat} {s : State} (hlt : nb s₀ - 16 * (e - 1) < 32)
    (hI : EInvTo s₀ P e s) :
    WP isa (tailE [.alu .add .r8 (.reg .rdx)] .r8) s (EPostTo s₀) := by
  have h1 := hI.one
  have hle := hI.a.le
  refine WP.seq (WP.mono (cmpE16To_ok hI hlt) fun s₁ ⟨hI₁, z₁⟩ => ?_)
  refine WP.ite (decide (nb s₀ = 16 * e)) (by simp only [eval, z₁]) (fun h => ?_) (fun h => ?_)
  · exact StitchTo.finalTo_ok hp hf (by simpa using h) hI₁
  · have hne : nb s₀ ≠ 16 * e := by simpa using h
    exact WP.seq (WP.mono (lastGRTo_ok hp hf (by omega_arith) hI₁) fun s₂ hI₂ =>
      remETo_ok hp hc hr hI₂ (by omega_arith) hne)

/-- `encToR` after the setup, for any number of blocks from 16 on. -/
theorem encTailRTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (hc : CtxPow s₀ (oR s₀))
    {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) (hr : RemLaw (hk s₀) (powC s₀)) {s : State} (hR : ReadyTo s₀ P s) :
    WP isa (.seq firstTo (.seq (.block [.alu .cmp .r9 (.imm 32)])
      (.seq (.ite .b (.block []) (.loop bodyTo .ae)) (tailE [.alu .add .r8 (.reg .rdx)] .r8)))) s
      (EPostTo s₀) := by
  refine WP.seq (WP.mono (StitchTo.firstTo_ok hp hR) fun s₂ hI₂ => ?_)
  refine WP.seq (WP.mono (StitchTo.cmpE_ok hI₂) fun s₃ ⟨hI₃, hcf⟩ => ?_)
  exact WP.seq (WP.mono (loopERTo_ok hp hf hI₃ hcf) fun s₄ ⟨e, hlt, hI₄⟩ => tailERTo_ok hp hc hf hr hlt hI₄)

end VG.Proof.Gcm.X86_64.StitchR

end

end

/-! ### `Gcm.X86_64.StitchR.Zero`, which only this module used -/

section

/-!
# The prepared 256-bit loops on fewer blocks than a group

`decR` and `encR` take any number of blocks from 1 on: `cmp r9, 16` sends
fewer than 16 blocks to `remD` or `remE` at once, without the loop, after a
setup without the powers (`setupS_ok`), from the state of the blocks after no
group; and 16 or more to the loops, as before, for which `SPre.ofLe` gives
back the 16 blocks their proofs assume (`zeroTail_ok`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchR

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost DInv AInv Ready FinOk nb pp cp dp
  hk y₀ ctb)
open VG.Impl.Gcm.X86_64.Stitch (ordD ordE dbody body first storeCtr storeY)
open VG.Impl.Gcm.X86_64.StitchR (remD remE tailE)
open VG.Proof.Gcm.X86_64.StitchZH (add9_ok)
open VG.Spec.Gcm (Block ghashFrom)

/-- `cmp r9, 16`. -/
theorem cmp9_ok (s : State) :
    WP isa (.block [.alu .cmp .r9 (.imm 16)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .r9).toNat < 16)) ∧ s'.gpr = s.gpr ∧ (∀ r l, s'.lane r l = s.lane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain e16 : BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 16 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    e16, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial, fun _ _ => rfl, trivial, trivial, trivial⟩

/-- `r9 + 16`, for the number of blocks in `r9`. -/
theorem r9_add16 {s₀ : State} : s₀.gpr .r9 + 16 = BitVec.ofNat 64 (16 + (nb s₀ - 16 * 0)) := by
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show (16 : BitVec 64).toNat = 16 from rfl, BitVec.toNat_ofNat]
  show ((nb s₀) + 16) % 2 ^ 64 = (16 + (nb s₀ - 16 * 0)) % 2 ^ 64
  rw [Nat.mul_zero, Nat.sub_zero, Nat.add_comm]

/-- The blocks before the first group: none decrypted or hashed. -/
theorem dinv0 {s₀ : State} {P : Nat → Nat → Block} {s : State} (hR : Ready s₀ P s) : DInv s₀ P 0 s :=
  ⟨hR.a, by rw [hR.rdx]; simp, by rw [hR.gpr _ (by decide) (by decide) (by decide)]; simp, hR.rax,
    fun r h1 h2 _ h4 => hR.gpr r h1 h2 h4, hR.pw, hR.m1, by rw [hR.y]; simp [ghashFrom], hR.y1⟩

/-- After the setup: `cmp r9, 16`, then fewer blocks than a group by
`small`, the others by `big`. -/
theorem zeroTail_ok {s₀ : State} {Rdy : State → Prop} {Q : State → Prop} {small big : Prog isa}
    (hkeep : ∀ s s', Rdy s → s'.gpr = s.gpr → (∀ r k, s'.lane r k = s.lane r k) → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → Rdy s')
    (h9 : ∀ s, Rdy s → s.gpr .r9 = s₀.gpr .r9)
    (hsmall : nb s₀ < 16 → ∀ s, Rdy s → WP isa small s Q) (hbig : 16 ≤ nb s₀ → ∀ s, Rdy s → WP isa big s Q)
    {s : State} (hR : Rdy s) :
    WP isa (.seq (.block [.alu .cmp .r9 (.imm 16)]) (.ite .b small big)) s Q := by
  refine WP.seq (WP.mono (cmp9_ok s) fun s' ⟨cf, g, l, m, rd, wr⟩ => ?_)
  obtain hR' := hkeep s s' hR g l m rd wr
  rw [h9 s hR] at cf
  refine WP.ite (decide (nb s₀ < 16)) (by simp only [eval, cf]) (fun h => ?_) (fun h => ?_)
  · exact hsmall (by simpa using h) s' hR'
  · exact hbig (by simp at h; omega_using [h]) s' hR'

end VG.Proof.Gcm.X86_64.StitchR

end

end


/-!
# The 256-bit interleaved loops with prepared powers meet their contracts

Untrusted: everything here is checked by Lean. `StitchR.setup` loads the
pairs of powers as `StitchZR.setupGP_ok` says, which `Stitch.setupG_ok`'s
postcondition is, with `x · H'ⁿ = Hⁿ` for `H'ⁿ = Hⁿ · x⁻¹` (`x_φ_hInvF`);
the rest of the setup and the loops are `Stitch`'s (`setupT_ok`,
`encTail_ok`, `decTail_ok`), and out of place `StitchTo`'s.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchR

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch (nb SPre SPreM SPreTo SPrePrepared StitchOkM StitchToOkM CtxMode EPost DPost
  EPostTo hk Ready setupT_ok finE finD)
open VG.Proof.Gcm.X86_64.StitchTo (ReadyTo)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF)
open VG.Spec.Gcm (Block hpow ghashFrom)
open VG.Proof.Gcm.X86_64.Pclmul (Prod φ_reduceB)
open VG.Proof.Gcm.X86_64.StitchZH (accR)

/-- `Hⁿ · x⁻¹`, times `x`, is `Hⁿ`. -/
theorem x_φ_hInvF (H : Block) (n : Nat) : x * φ (hInvF (hpow H n)) = φ H ^ n := by
  rw [hInvF, Pclmul.x_φ_hInv, φ_hpow]

/-- The setup: the state the loops start from, as `Stitch.setup_ok`. -/
theorem setup_ok {s₀ : State} {lo np : Nat} (hp : SPrePrepared s₀ lo np) (h8 : 8 ≤ np := by decide) :
    WP isa (.block Impl.Gcm.X86_64.StitchR.setup) s₀ fun s => ∃ P, Ready s₀ P s ∧
      ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ (hk s₀) ^ (16 - 2 * k - l) := by
  simp only [Impl.Gcm.X86_64.StitchR.setup, List.append_assoc]
  rw [WP.block_append_iff]
  exact WP.mono (StitchZR.setupGP_ok hp h8) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ =>
    WP.mono (setupT_ok hp.base l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR =>
      ⟨_, hR, fun k hk l hl => by rw [pw k hk l hl]; exact x_φ_hInvF _ _⟩

/-- The prepared powers, `H'¹⁶⁻ᵐ` at `16 m`: the products of the last `r`
blocks with `H'ʳ` … `H'`, reduced, add up to `GHASH` over them. -/
theorem remLaw {H : Block} {P : Nat → Nat → Block}
    (hP : ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ H ^ (16 - 2 * k - l)) : RemLaw H P := by
  intro r hr1 hr15 X y
  let T : Nat → BitVec 128 := fun j => P ((16 - r + j) / 2) ((16 - r + j) % 2)
  obtain hT : ∀ j < r, x * φ (T j) = φ H ^ (r - j) := fun j hj => by
    have := hP ((16 - r + j) / 2) (by omega_using [hr15, hj]) ((16 - r + j) % 2) (by omega_using [])
    rwa [show 16 - 2 * ((16 - r + j) / 2) - (16 - r + j) % 2 = r - j by omega_using [hr15]] at this
  obtain key : ∀ n, 1 ≤ n → n ≤ r →
      (accR X T y n).val = φ H ^ (r - n) * φ (ghashFrom H y ((List.range n).map X)) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ n ih =>
      intro _ hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · have h0 := hT 0 (by omega_using [hr1])
        simp only [accR, ↓reduceIte, Prod.val_acc, Prod.val_zero, zero_add, List.range_one, List.map_cons,
          List.map_nil, ghashFrom, List.foldl_cons, List.foldl_nil, φ_mul, Nat.sub_zero] at h0 ⊢
        rw [show r = (r - (0 + 1)) + 1 by omega_using [hr1], pow_succ] at h0
        linear_combination φ (y ^^^ X 0) * h0
      · have hn' := hT n (by omega_using [hn])
        rw [show r - n = (r - (n + 1)) + 1 by omega_using [hn], pow_succ] at hn'
        simp only [accR, show n ≠ 0 by omega_using [hpos], ↓reduceIte, Prod.val_acc, ih hpos (by omega_using [hn]), List.range_succ,
          List.map_append, List.map_cons, List.map_nil, ghashFrom, List.foldl_append, List.foldl_cons,
          List.foldl_nil, φ_mul, φ_xor, φ_zero, zero_add]
        rw [show r - n = (r - (n + 1)) + 1 by omega_using [hn], pow_succ]
        linear_combination φ (X n) * hn'
  apply φ_inj
  rw [φ_reduceB, key r hr1 (Nat.le_refl _), Nat.sub_self, pow_zero, one_mul]

/-! ## Encryption: no copy of the powers left

`encR` reads the powers of the blocks after the last group from the key
context (`remE`): with fewer than 16 blocks it makes no copy of them
(`setupS`), and otherwise clears the copy the loops read once they end
(`zeroPow`). -/

/-- What `remE` needs of a prepared key context with at least eight pairs. -/
theorem _root_.VG.Proof.Gcm.X86_64.Stitch.SPrePrepared.ctxPow {s₀ : State} {lo np : Nat} (hp : SPrePrepared s₀ lo np) (h8 : 8 ≤ np) :
    CtxPow s₀ (Stitch.dR s₀) where
  k_in := by obtain ⟨r, hr, hc⟩ := hp.k_in; exact ⟨r, hr, by unfold Region.Contains at hc ⊢; omega_using [hc]⟩
  wrap_k := by have := hp.wrap_k; omega_using [this]
  d_k := hp.d_k.sub_right (Region.sub_prefix (by decide))
  p_k := hp.p_k.sub_right (Region.sub_prefix (by decide))
  c_k := hp.c_k.sub_right (Region.sub_prefix (by decide))
  pow := fun k hk => hp.pow k (by omega_using [hk, h8])

/-- The same, out of place. -/
theorem _root_.VG.Proof.Gcm.X86_64.Stitch.SPreTo.ctxPow {s₀ : State} {np : Nat} {hn : 8 ≤ np ∧ np ≤ 24} (hp : SPreTo (CtxMode.preparedN np hn) s₀)
    (h8 : 8 ≤ np) : CtxPow s₀ (Stitch.oR s₀) where
  k_in := by
    obtain ⟨r, hr, hc⟩ := hp.k_in
    have hl : (CtxMode.preparedN np hn).len = 1024 := rfl
    exact ⟨r, hr, by unfold Region.Contains at hc ⊢; omega_using [hc, hl]⟩
  wrap_k := by have := hp.wrap_k; change _ + 1024 ≤ _ at this; omega_using [this]
  d_k := hp.k_o.symm.sub_right (Region.sub_prefix (show 512 ≤ 1024 by decide))
  p_k := hp.k_p.symm.sub_right (Region.sub_prefix (show 512 ≤ 1024 by decide))
  c_k := hp.k_c.symm.sub_right (Region.sub_prefix (show 512 ≤ 1024 by decide))
  pow := fun k hk => hp.ok k (by omega_using [hk, h8])

/-- `remLaw` for the powers the prepared pairs hold. -/
theorem remLawC (s₀ : State) : RemLaw (hk s₀) (powC s₀) :=
  remLaw (P := powC s₀) fun k _ l _ => x_φ_hInvF (hk s₀) (16 - 2 * k - l)

/-- The precondition, of a state with the same registers, memory and regions. -/
theorem _root_.VG.Proof.Gcm.X86_64.Stitch.SPrePrepared.congr {s s₀ : State} {lo np : Nat} (h : SPrePrepared s₀ lo np) (g : s.gpr = s₀.gpr)
    (m : s.mem = s₀.mem) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) : SPrePrepared s lo np := by
  cases s; cases s₀; simp only at g m rd wr; subst g m rd wr
  exact { h with base := { h.base with } }

/-- The postcondition, of a state with the same registers, memory and regions. -/
theorem _root_.VG.Proof.Gcm.X86_64.Stitch.EPost.congr {s s₀ t : State} (h : EPost s t) (g : s.gpr = s₀.gpr) (m : s.mem = s₀.mem)
    (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) : EPost s₀ t := by
  cases s; cases s₀; simp only at g m rd wr; subst g m rd wr
  exact { h with }

/-- The same, of the decryption. -/
theorem _root_.VG.Proof.Gcm.X86_64.Stitch.DPost.congr {s s₀ t : State} (h : DPost s t) (g : s.gpr = s₀.gpr) (m : s.mem = s₀.mem)
    (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) : DPost s₀ t := by
  cases s; cases s₀; simp only at g m rd wr; subst g m rd wr
  exact { h with }

/-- `setupS`, then `r9` raised by 16: the state `remE` starts from, the
blocks after no group. -/
theorem setupS_okF {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) :
    WP isa (.block (Impl.Gcm.X86_64.StitchR.setupS ++ ([.alu .add .r9 (.imm 16)] : List Instr))) s₀ fun s =>
      EInvR s₀ (fun k l => s₀.mem.readW (Stitch.pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128) 0 s ∧
        s.mem = s₀.mem := by
  simp only [Impl.Gcm.X86_64.StitchR.setupS, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pclmul.const_ok .xmm0 _ s₀ (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pclmul.const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  obtain o₁₂ := o₁.trans o₂
  rw [show ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] : List Instr) ++
      (Impl.Gcm.X86_64.Stitch.setupC ++ ([.alu .add .r9 (.imm 16)] : List Instr)) =
    [.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1)] ++ ([.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] ++
      (Impl.Gcm.X86_64.Stitch.setupC ++ ([.alu .add .r9 (.imm 16)] : List Instr))) from rfl, WP.block_append_iff]
  refine WP.mono (StitchZP.vinsSelf_ok .xmm0 s₂) fun s₃ ⟨v₃, f₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (StitchZP.vinsSelf_ok .xmm1 s₃) fun s₄ ⟨v₄, f₄⟩ => ?_
  obtain m0 : ∀ l < 2, s₄.lane .xmm0 l = revMask := fun l hl => by
    rw [f₄.lane _ (by decide) l hl, v₃ l hl]; show s₂.xmm .xmm0 = _; rw [o₂.xmm _ (by decide), c₁]; rfl
  obtain m1 : ∀ l < 2, s₄.lane .xmm1 l = Impl.Gcm.X86_64.Pclmul.poly := fun l hl => by
    rw [v₄ l hl, f₃.lane _ (by decide) 0 (by decide)]; exact c₂
  obtain g₄ : ∀ r, r ≠ .rax → s₄.gpr r = s₀.gpr r := fun r hr => by rw [f₄.gpr, f₃.gpr, o₁₂.gpr r hr]
  obtain mm₄ : s₄.mem = s₀.mem := by rw [f₄.mem, f₃.mem, o₁₂.mem]
  obtain rd₄ : s₄.rd = s₀.rd := by rw [f₄.rd, f₃.rd, o₁₂.rd]
  obtain wr₄ : s₄.wr = s₀.wr := by rw [f₄.wr, f₃.wr, o₁₂.wr]
  rw [WP.block_append_iff]
  refine WP.mono (Stitch.setupC_ok s₄ m0 (by rw [wr₄, g₄ _ (by decide)]; exact hp.y_in)
    (by rw [wr₄, g₄ _ (by decide)]; exact hp.c_in))
    fun s₅ ⟨y0, y1, c14, c15, r10, rax, rdx, gk, lk, m₅, rd₅, wr₅⟩ => ?_
  refine WP.mono (StitchZH.add9_ok s₅) fun s₆ ⟨a9, g₆, l₆, m₆, rd₆, wr₆⟩ => ?_
  obtain l6 : ∀ x l, l < 2 → s₆.lane x l = s₅.lane x l := fun x l hl => by
    rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl, l₆]
  obtain gs : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → r ≠ .r9 → s₆.gpr r = s₀.gpr r := fun r h1 h2 h3 h9 => by
    rw [g₆ r h9, gk r h1 h2 h3, g₄ r h1]
  obtain hm : s₆.mem = s₀.mem := by rw [m₆, m₅, mm₄]
  refine ⟨?_, hm⟩
  exact
    { a := ⟨Nat.zero_le _, fun l hl => by rw [l6 _ _ hl, c14 l hl, g₄ _ (by decide), mm₄, Nat.zero_add],
        fun l hl => by rw [l6 _ _ hl, lk _ (by decide) (by decide) (by decide) (by decide) l hl]; exact m0 l hl,
        fun l hl => by rw [l6 _ _ hl]; exact c15 l hl,
        by rw [gs _ (by decide) (by decide) (by decide) (by decide)],
        by rw [gs _ (by decide) (by decide) (by decide) (by decide)],
        by rw [g₆ _ (by decide), r10, g₄ _ (by decide), g₄ _ (by decide)],
        by rw [hm]; exact Frame.refl _ _,
        fun k hk => by rw [hm]; simp only [Nat.mul_zero, Nat.not_lt_zero, ite_false],
        by rw [rd₆, rd₅, rd₄], by rw [wr₆, wr₅, wr₄]⟩
      rdx := by rw [g₆ _ (by decide), rdx, g₄ _ (by decide)]; simp
      r9 := by rw [a9, gk _ (by decide) (by decide) (by decide), g₄ _ (by decide)]; exact r9_add16
      rax := by rw [g₆ _ (by decide), rax, g₄ _ (by decide)]
      gpr := fun r h1 h2 h3 h4 => gs r h1 h2 h4 h3
      pw := fun k hk j hj => by rw [hm]
      m1 := fun l hl => by rw [l6 _ _ hl, lk _ (by decide) (by decide) (by decide) (by decide) l hl]; exact m1 l hl
      y := by rw [l6 _ _ (by decide), y0, g₄ _ (by decide), mm₄]; simp [ghashFrom]
      y1 := by rw [l6 _ _ (by decide)]; exact y1 }

theorem setupS_ok {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) :
    WP isa (.block (Impl.Gcm.X86_64.StitchR.setupS ++ ([.alu .add .r9 (.imm 16)] : List Instr))) s₀
      (EInvR s₀ (fun k l => s₀.mem.readW (Stitch.pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128) 0) :=
  WP.mono (setupS_okF hp) fun _ h => h.1

/-- Encryption of fewer blocks than a group: no copy of the powers, all of
them by `remE`. -/
theorem encSmallC_ok {s₀ : State} {np : Nat} (hp : SPrePrepared s₀ 1 np) (h8 : 8 ≤ np) (h1 : 1 ≤ nb s₀)
    (hlt : nb s₀ < 16) :
    WP isa (.seq (.block (Impl.Gcm.X86_64.StitchR.setupS ++ ([.alu .add .r9 (.imm 16)] : List Instr)))
      (Impl.Gcm.X86_64.StitchR.remE .rdx)) s₀ (EPost s₀) :=
  WP.seq (WP.mono (setupS_ok hp.base) fun _ hI =>
    remE_ok hp.base (hp.ctxPow h8) (remLawC s₀) (e := 0) hI (by omega_using [hlt]) (by omega_using [h1]))

/-- Encryption of a group or more: the loops, as `Stitch.enc`, then the copy
of the powers cleared. -/
theorem encBig_ok {s₀ : State} {np : Nat} (hp : SPrePrepared s₀ 16 np) (h8 : 8 ≤ np) :
    WP isa (.seq (.block Impl.Gcm.X86_64.StitchR.setup) (.seq Impl.Gcm.X86_64.Stitch.first
      (.seq (.block [.alu .cmp .r9 (.imm 32)]) (.seq (.ite .b (.block []) (.loop Impl.Gcm.X86_64.Stitch.body .ae))
        (.seq (Impl.Gcm.X86_64.StitchR.tailE [] .rdx) (.block Impl.Gcm.X86_64.Stitch.zeroPow)))))) s₀ (EPost s₀) := by
  refine WP.seq (WP.mono (setup_ok hp h8) fun s ⟨P, hR, hpw⟩ => ?_)
  refine WP.seq (WP.mono (Stitch.first_ok hp.base hR) fun s₂ hI₂ => ?_)
  refine WP.seq (WP.mono (Stitch.cmpE_ok hI₂) fun s₃ ⟨hI₃, hcf⟩ => ?_)
  refine WP.seq (WP.mono (loopER_ok hp.base (finE hpw) hI₃ hcf) fun s₄ ⟨e, hlt, hI₄⟩ => ?_)
  exact WP.seq (WP.mono (tailER_ok hp.base (hp.ctxPow h8) (finE hpw) (remLawC s₀) hlt hI₄) fun s₅ h₅ =>
    Stitch.zeroPow_ok hp.base h₅)

/-- `encR`: the encryption of any number of blocks from 1 on. -/
theorem encR_ok {s₀ : State} {np : Nat} (hp : SPrePrepared s₀ 1 np) (h8 : 8 ≤ np := by decide) :
    WP isa Impl.Gcm.X86_64.StitchR.encR s₀ (EPost s₀) := by
  refine zeroTail_ok (Rdy := fun s => s.gpr = s₀.gpr ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr)
    (fun _ _ ⟨g, m, rd, wr⟩ g' _ m' rd' wr' => ⟨g'.trans g, m'.trans m, rd'.trans rd, wr'.trans wr⟩)
    (fun _ ⟨g, _⟩ => by rw [g]) (fun hlt s ⟨g, m, rd, wr⟩ => ?_) (fun h16 s ⟨g, m, rd, wr⟩ => ?_) ⟨rfl, rfl, rfl, rfl⟩
  · have hn : nb s = nb s₀ := by simp only [nb, g]
    exact WP.mono (encSmallC_ok (hp.congr g m rd wr) h8 (by rw [hn]; exact hp.base.nb16) (by rw [hn]; exact hlt))
      fun t ht => ht.congr g m rd wr
  · have hn : nb s = nb s₀ := by simp only [nb, g]
    exact WP.mono (encBig_ok ({ hp.congr g m rd wr with base := (hp.congr g m rd wr).base.ofLe (by rw [hn]; exact h16) }) h8)
      fun t ht => ht.congr g m rd wr

/-- The out-of-place setup, as `StitchTo.setupTo_ok`. -/
theorem setupTo_ok {s₀ : State} {np : Nat} {hn : 8 ≤ np ∧ np ≤ 24} (hp : SPreTo (CtxMode.preparedN np hn) s₀)
    (h8 : 8 ≤ np := by decide) :
    WP isa (.block Impl.Gcm.X86_64.StitchR.setupTo) s₀ fun s => ∃ P, ReadyTo s₀ P s ∧
      ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ (hk s₀) ^ (16 - 2 * k - l) := by
  rw [Impl.Gcm.X86_64.StitchR.setupTo, List.append_assoc, WP.block_append_iff]
  refine WP.mono (StitchZRTo.setupGPTo_ok hp h8) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  exact WP.mono (StitchZTo.setupTTo_ok hp l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR =>
    ⟨_, ReadyTo.ofReady2 hR, fun k hk l hl => by rw [pw k hk l hl]; exact x_φ_hInvF _ _⟩

/-- The out-of-place loop, for a prepared key context, for any number of
blocks from 16 on. -/
theorem stitchTo_okN (np : Nat) (hn : 8 ≤ np ∧ np ≤ 24 := by decide) (h8 : 8 ≤ np := by decide) :
    StitchToOkM (CtxMode.preparedN np hn) Impl.Gcm.X86_64.StitchR.encToR 1 := fun _ hp _ =>
  WP.seq (WP.mono (setupTo_ok hp h8) fun _ ⟨_, hR, hpw⟩ =>
    encTailRTo_ok hp (hp.ctxPow h8) (finE hpw) (remLawC _) hR)

/-- The setup's powers give the products of an encryption body. -/
theorem stitchTo_ok : StitchToOkM CtxMode.prepared Impl.Gcm.X86_64.StitchR.encToR 1 := stitchTo_okN 24

theorem setupFinN (np : Nat) (hn : 8 ≤ np ∧ np ≤ 24 := by decide) (h8 : 8 ≤ np := by decide) : SetupFin np hn := fun hp =>
  WP.mono (setupTo_ok hp h8) fun _ ⟨P, hR, hpw⟩ => ⟨P, hR, finE hpw⟩

/-! ## What `encR` leaves in its working space -/

/-- The bytes of its working space that `encR` clears, of `n` blocks (from 1
on): the copy of the powers, with at least 16, and the keystream of the
blocks after the last group, 128 bytes at `256`, or 256 if more than 8. -/
def zeroR (n i : Nat) : Bool :=
  (decide (16 ≤ n) && decide (i < 256)) ||
    (decide (n % 16 ≠ 0) && decide (256 ≤ i) && (decide (i < 384) || decide (8 < n % 16)))

/-- `setup_ok`, and what the setup writes: the powers, at `scratch`. -/
theorem setup_okF {s₀ : State} {lo np : Nat} (hp : SPrePrepared s₀ lo np) (h8 : 8 ≤ np := by decide) :
    WP isa (.block Impl.Gcm.X86_64.StitchR.setup) s₀ fun s => ∃ P, Ready s₀ P s ∧
      (∀ k < 8, ∀ l < 2, x * φ (P k l) = φ (hk s₀) ^ (16 - 2 * k - l)) ∧
      Frame [⟨Stitch.pp s₀, 256⟩] s₀.mem s.mem := by
  simp only [Impl.Gcm.X86_64.StitchR.setup, List.append_assoc]
  rw [WP.block_append_iff]
  exact WP.mono (StitchZR.setupGP_ok hp h8) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ =>
    WP.mono (Stitch.setupT_okF hp.base l0 l1 g₁ m₁ rd₁ wr₁) fun _ ⟨hR, f⟩ =>
      ⟨_, hR, fun k hk l hl => by rw [pw k hk l hl]; exact x_φ_hInvF _ _, f⟩

/-- A byte of the working space is apart from the counter, `Y` and the data. -/
theorem notIn_p {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) {i : Nat} (hi : i < 1024) :
    ∀ r ∈ [Stitch.cR s₀, Stitch.yR s₀, Stitch.dR s₀], ¬ r.Contains (Stitch.pp s₀ + BitVec.ofNat 64 i) 1 := by
  have hwp := hp.wrap_p
  obtain hxP : (Stitch.pR s₀).Contains (Stitch.pp s₀ + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  intro r hr hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.p_c _ hxP hc
  · exact hp.p_y _ hxP hc
  · exact hp.d_p _ hc hxP

/-- Byte `i` of the working space is not in its first `k`, nor in the `k'`
from `d` on, if `i` is not. -/
theorem notIn_off (p : Addr) {d k i : Nat} (hk : d + k ≤ 2 ^ 64) (hi : i < 2 ^ 64) (h : ¬ (d ≤ i ∧ i < d + k)) :
    ¬ (⟨p + BitVec.ofNat 64 d, k⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 := fun hc => by
  change (p + BitVec.ofNat 64 i - (p + BitVec.ofNat 64 d)).toNat < k at hc
  rw [Offset.lt_iff _ _ hk, Mem.sub_ofNat_toNat _ hi] at hc
  exact h hc

theorem notIn_base (p : Addr) {k i : Nat} (hi : i < 2 ^ 64) (h : k ≤ i) :
    ¬ (⟨p, k⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 := fun hc => by
  change (p + BitVec.ofNat 64 i - p).toNat + 1 ≤ k at hc
  rw [Mem.sub_ofNat_toNat _ hi] at hc
  omega_arith

/-- What `encR` writes, all of it in its first 512 bytes of working space. -/
theorem frame512 {s₀ : State} :
    ∀ r ∈ [⟨Stitch.pp s₀ + BitVec.ofNat 64 256, 256⟩, ⟨Stitch.pp s₀, 256⟩, Stitch.cR s₀, Stitch.yR s₀, Stitch.dR s₀],
      ∃ r' ∈ [Stitch.cR s₀, Stitch.yR s₀, Stitch.dR s₀, (⟨Stitch.pp s₀, 512⟩ : Region)], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨Stitch.pp s₀, 512⟩, by simp, Offset.sub_base _ (by decide)⟩
  · exact ⟨⟨Stitch.pp s₀, 512⟩, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨Stitch.cR s₀, by simp, fun _ h => h⟩
  · exact ⟨Stitch.yR s₀, by simp, fun _ h => h⟩
  · exact ⟨Stitch.dR s₀, by simp, fun _ h => h⟩

/-- Encryption of fewer blocks than a group, and what it leaves in its
working space. -/
theorem encSmallC_okL {s₀ : State} {np : Nat} (hp : SPrePrepared s₀ 1 np) (h8 : 8 ≤ np) (h1 : 1 ≤ nb s₀)
    (hlt : nb s₀ < 16) :
    WP isa (.seq (.block (Impl.Gcm.X86_64.StitchR.setupS ++ ([.alu .add .r9 (.imm 16)] : List Instr)))
      (Impl.Gcm.X86_64.StitchR.remE .rdx)) s₀ fun s => EPost s₀ s ∧ Stitch.PieceL 512 zeroR s₀ s := by
  have hwp := hp.base.wrap_p
  refine WP.seq (WP.mono (setupS_okF hp.base) fun s ⟨hI, hm⟩ => ?_)
  refine WP.mono (remE_okF hp.base (hp.ctxPow h8) (remLawC s₀) (e := 0) hI (by omega_using [hlt])
    (by omega_using [h1])) fun s' ⟨h, f, b⟩ => ⟨h, ?_, fun i hi => ?_⟩
  · rw [hm] at f
    exact (f.sub fun r hr => frame512 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h <;> simp [h]))
  · by_cases h256 : i < 256
    · have hz : zeroR (nb s₀) i = false := by
        simp only [zeroR, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega_arith
      simp only [hz, Bool.false_eq_true, ↓reduceIte]
      rw [f _ fun r hr => ?_, hm]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact notIn_p hp.base (by omega_arith) _ (by simp)
      · exact notIn_p hp.base (by omega_arith) _ (by simp)
      · exact notIn_p hp.base (by omega_arith) _ (by simp)
      · exact notIn_off _ (by decide) (by omega_arith) (by omega_arith)
    · have b' := b (i - 256) (by omega_arith)
      rw [show 256 + (i - 256) = i by omega_arith, hm] at b'
      rw [b']
      obtain e : (i - 256 < 128 ∨ 8 < nb s₀ - 16 * 0) ↔ zeroR (nb s₀) i = true := by
        simp only [zeroR, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega_arith
      by_cases hz : i - 256 < 128 ∨ 8 < nb s₀ - 16 * 0
      · simp only [hz, e.mp hz, ↓reduceIte]
      · have hz' : zeroR (nb s₀) i = false := by
          cases h : zeroR (nb s₀) i
          · rfl
          · exact absurd (e.mpr h) hz
        simp only [hz, hz', Bool.false_eq_true, ↓reduceIte]

/-- Encryption of a group or more, and what it leaves in its working space:
the copy of the powers cleared, and `remE`'s keystream if any. -/
theorem encBig_okL {s₀ : State} {np : Nat} (hp : SPrePrepared s₀ 16 np) (h8 : 8 ≤ np) :
    WP isa (.seq (.block Impl.Gcm.X86_64.StitchR.setup) (.seq Impl.Gcm.X86_64.Stitch.first
      (.seq (.block [.alu .cmp .r9 (.imm 32)]) (.seq (.ite .b (.block []) (.loop Impl.Gcm.X86_64.Stitch.body .ae))
        (.seq (Impl.Gcm.X86_64.StitchR.tailE [] .rdx) (.block Impl.Gcm.X86_64.Stitch.zeroPow)))))) s₀
      fun s => EPost s₀ s ∧ Stitch.PieceL 512 zeroR s₀ s := by
  have hwp := hp.base.wrap_p
  have h16 := hp.base.nb16
  refine WP.seq (WP.mono (setup_okF hp h8) fun s ⟨P, hR, hpw, f₁⟩ => ?_)
  refine WP.seq (WP.mono (Stitch.first_okF hp.base hR) fun s₂ ⟨hI₂, f₂⟩ => ?_)
  refine WP.seq (WP.mono (Stitch.cmpE_okF hI₂) fun s₃ ⟨⟨hI₃, hcf⟩, m₃⟩ => ?_)
  refine WP.seq (WP.mono (loopER_okF hp.base (finE hpw) hI₃ hcf) fun s₄ ⟨⟨e, hlt, hI₄⟩, f₄⟩ => ?_)
  have h1e := hI₄.one
  have hle := hI₄.a.le
  refine WP.seq (WP.mono (tailER_okF hp.base (hp.ctxPow h8) (finE hpw) (remLawC s₀) hlt hI₄)
    fun s₅ ⟨h₅, f₅, b₅⟩ => ?_)
  obtain h11 : s₅.gpr .r11 = Stitch.pp s₀ := h₅.gpr _ (by decide) (by decide) (by decide) (by decide)
  refine WP.mono (Stitch.wp_and (Stitch.zeroPow_ok hp.base h₅) (Stitch.zeroPow_zero hp.base h11 h₅.wr))
    fun s₆ ⟨h₆, f₆, z₆⟩ => ⟨h₆, ?_, fun i hi => ?_⟩
  · rw [m₃] at f₄
    obtain F : Frame [⟨Stitch.pp s₀ + BitVec.ofNat 64 256, 256⟩, ⟨Stitch.pp s₀, 256⟩, Stitch.cR s₀, Stitch.yR s₀,
        Stitch.dR s₀] s₀.mem s₆.mem := by
      obtain m1 : ∀ r ∈ [(⟨Stitch.pp s₀, 256⟩ : Region)], r ∈ [⟨Stitch.pp s₀ + BitVec.ofNat 64 256, 256⟩,
          ⟨Stitch.pp s₀, 256⟩, Stitch.cR s₀, Stitch.yR s₀, Stitch.dR s₀] := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp
      obtain m2 : ∀ r ∈ [Stitch.dR s₀], r ∈ [⟨Stitch.pp s₀ + BitVec.ofNat 64 256, 256⟩,
          ⟨Stitch.pp s₀, 256⟩, Stitch.cR s₀, Stitch.yR s₀, Stitch.dR s₀] := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp
      exact ((((f₁.mono m1).trans (f₂.mono m2)).trans (f₄.mono m2)).trans (f₅.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp)).trans (f₆.mono m1)
    exact F.sub (frame512)
  · by_cases h256 : i < 256
    · have hz : zeroR (nb s₀) i = true := by
        simp only [zeroR, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega_arith
      simp only [hz, ↓reduceIte]; exact z₆ i h256
    · have k6 : s₆.mem (Stitch.pp s₀ + BitVec.ofNat 64 i) = s₅.mem (Stitch.pp s₀ + BitVec.ofNat 64 i) :=
        f₆ _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact notIn_base _ (by omega_arith) (by omega_arith)
      obtain nD : ∀ r ∈ [Stitch.dR s₀], ¬ r.Contains (Stitch.pp s₀ + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact notIn_p hp.base (by omega_arith) _ (by simp)
      obtain k4 : s₄.mem (Stitch.pp s₀ + BitVec.ofNat 64 i) = s₀.mem (Stitch.pp s₀ + BitVec.ofNat 64 i) := by
        rw [f₄ _ nD, m₃, f₂ _ nD, f₁ _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact notIn_base _ (by omega_arith) (by omega_arith)]
      obtain b' := b₅ (i - 256) (by omega_arith)
      rw [show 256 + (i - 256) = i by omega_arith, k4] at b'
      rw [k6, b']
      obtain e' : (nb s₀ ≠ 16 * e ∧ (i - 256 < 128 ∨ 8 < nb s₀ - 16 * e)) ↔ zeroR (nb s₀) i = true := by
        simp only [zeroR, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega_arith
      by_cases hz : nb s₀ ≠ 16 * e ∧ (i - 256 < 128 ∨ 8 < nb s₀ - 16 * e)
      · simp only [hz, e'.mp hz, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
      · have hz' : zeroR (nb s₀) i = false := by
          cases h : zeroR (nb s₀) i
          · rfl
          · exact absurd (e'.mpr h) hz
        simp only [hz, hz', Bool.false_eq_true, ↓reduceIte]

/-- `encR`, and what it leaves in its working space (`zeroR`). -/
theorem encR_okL {s₀ : State} {np : Nat} (hp : SPrePrepared s₀ 1 np) (h8 : 8 ≤ np := by decide) :
    WP isa Impl.Gcm.X86_64.StitchR.encR s₀ fun s => EPost s₀ s ∧ Stitch.PieceL 512 zeroR s₀ s := by
  refine zeroTail_ok (Rdy := fun s => s.gpr = s₀.gpr ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr)
    (fun _ _ ⟨g, m, rd, wr⟩ g' _ m' rd' wr' => ⟨g'.trans g, m'.trans m, rd'.trans rd, wr'.trans wr⟩)
    (fun _ ⟨g, _⟩ => by rw [g]) (fun hlt s ⟨g, m, rd, wr⟩ => ?_) (fun h16 s ⟨g, m, rd, wr⟩ => ?_) ⟨rfl, rfl, rfl, rfl⟩
  · have hn : nb s = nb s₀ := by simp only [nb, g]
    exact WP.mono (encSmallC_okL (hp.congr g m rd wr) h8 (by rw [hn]; exact hp.base.nb16) (by rw [hn]; exact hlt))
      fun t ⟨ht, hl⟩ => ⟨ht.congr g m rd wr, hl.congr g m⟩
  · have hn : nb s = nb s₀ := by simp only [nb, g]
    exact WP.mono (encBig_okL ({ hp.congr g m rd wr with base := (hp.congr g m rd wr).base.ofLe (by rw [hn]; exact h16) }) h8)
      fun t ⟨ht, hl⟩ => ⟨ht.congr g m rd wr, hl.congr g m⟩

/-! ## Decryption: no copy of the powers left

`decR` reads the powers of the blocks after the last group from the key
context (`remD`), as `encR` does, with fewer than 16 blocks makes no copy of
them (`setupS`), and otherwise clears the copy the loop reads once it ends
(`zeroPow`). -/

/-- Decryption of fewer blocks than a group, and what it leaves in its
working space: no copy of the powers, all of them by `remD`. -/
theorem decSmallC_okL {s₀ : State} {np : Nat} (hp : SPrePrepared s₀ 1 np) (h8 : 8 ≤ np) (h1 : 1 ≤ nb s₀)
    (hlt : nb s₀ < 16) :
    WP isa (.seq (.block (Impl.Gcm.X86_64.StitchR.setupS ++ ([.alu .add .r9 (.imm 16)] : List Instr)))
      Impl.Gcm.X86_64.StitchR.remD) s₀ fun s => DPost s₀ s ∧ Stitch.PieceL 512 zeroR s₀ s := by
  have hwp := hp.base.wrap_p
  refine WP.seq (WP.mono (setupS_okF hp.base) fun s ⟨hI, hm⟩ => ?_)
  refine WP.mono (remD_okF hp.base (hp.ctxPow h8) (remLawC s₀) (e := 0) hI.toD0 (by omega_using [hlt])
    (by omega_using [h1])) fun s' ⟨h, f, b⟩ => ⟨h, ?_, fun i hi => ?_⟩
  · rw [hm] at f
    exact (f.sub fun r hr => frame512 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h <;> simp [h]))
  · by_cases h256 : i < 256
    · have hz : zeroR (nb s₀) i = false := by
        simp only [zeroR, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega_arith
      simp only [hz, Bool.false_eq_true, ↓reduceIte]
      rw [f _ fun r hr => ?_, hm]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact notIn_p hp.base (by omega_arith) _ (by simp)
      · exact notIn_p hp.base (by omega_arith) _ (by simp)
      · exact notIn_p hp.base (by omega_arith) _ (by simp)
      · exact notIn_off _ (by decide) (by omega_arith) (by omega_arith)
    · have b' := b (i - 256) (by omega_arith)
      rw [show 256 + (i - 256) = i by omega_arith, hm] at b'
      rw [b']
      obtain e : (i - 256 < 128 ∨ 8 < nb s₀ - 16 * 0) ↔ zeroR (nb s₀) i = true := by
        simp only [zeroR, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega_arith
      by_cases hz : i - 256 < 128 ∨ 8 < nb s₀ - 16 * 0
      · simp only [hz, e.mp hz, ↓reduceIte]
      · have hz' : zeroR (nb s₀) i = false := by
          cases h : zeroR (nb s₀) i
          · rfl
          · exact absurd (e.mpr h) hz
        simp only [hz, hz', Bool.false_eq_true, ↓reduceIte]

/-- Decryption of a group or more, and what it leaves in its working space:
the loop, as `Stitch.dec`, then the copy of the powers cleared, and `remD`'s
keystream if any. -/
theorem decBig_okL {s₀ : State} {np : Nat} (hp : SPrePrepared s₀ 16 np) (h8 : 8 ≤ np) :
    WP isa (.seq (.block Impl.Gcm.X86_64.StitchR.setup) (.seq (.loop Impl.Gcm.X86_64.Stitch.dbody .ae)
      (.seq Impl.Gcm.X86_64.StitchR.tailD (.block Impl.Gcm.X86_64.Stitch.zeroPow)))) s₀
      fun s => DPost s₀ s ∧ Stitch.PieceL 512 zeroR s₀ s := by
  have hwp := hp.base.wrap_p
  have h16 := hp.base.nb16
  refine WP.seq (WP.mono (setup_okF hp h8) fun s ⟨P, hR, hpw, f₁⟩ => ?_)
  refine WP.seq (WP.mono (loopDR_okF hp.base (finD hpw) (dinv0 hR)) fun s₄ ⟨⟨e, hlt, hI₄⟩, f₄⟩ => ?_)
  have hle := hI₄.a.le
  refine WP.seq (WP.mono (dtailR_okF hp.base (hp.ctxPow h8) (remLawC s₀) hlt hI₄) fun s₅ ⟨h₅, f₅, b₅⟩ => ?_)
  obtain h11 : s₅.gpr .r11 = Stitch.pp s₀ := h₅.gpr _ (by decide) (by decide) (by decide) (by decide)
  refine WP.mono (Stitch.wp_and (Stitch.zeroPowD_ok hp.base h₅) (Stitch.zeroPow_zero hp.base h11 h₅.wr))
    fun s₆ ⟨h₆, f₆, z₆⟩ => ⟨h₆, ?_, fun i hi => ?_⟩
  · have F : Frame [⟨Stitch.pp s₀ + BitVec.ofNat 64 256, 256⟩, ⟨Stitch.pp s₀, 256⟩, Stitch.cR s₀, Stitch.yR s₀,
        Stitch.dR s₀] s₀.mem s₆.mem := by
      obtain m1 : ∀ r ∈ [(⟨Stitch.pp s₀, 256⟩ : Region)], r ∈ [⟨Stitch.pp s₀ + BitVec.ofNat 64 256, 256⟩,
          ⟨Stitch.pp s₀, 256⟩, Stitch.cR s₀, Stitch.yR s₀, Stitch.dR s₀] := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp
      obtain m2 : ∀ r ∈ [Stitch.dR s₀], r ∈ [⟨Stitch.pp s₀ + BitVec.ofNat 64 256, 256⟩,
          ⟨Stitch.pp s₀, 256⟩, Stitch.cR s₀, Stitch.yR s₀, Stitch.dR s₀] := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp
      exact (((f₁.mono m1).trans (f₄.mono m2)).trans (f₅.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp)).trans (f₆.mono m1)
    exact F.sub (frame512)
  · by_cases h256 : i < 256
    · have hz : zeroR (nb s₀) i = true := by
        simp only [zeroR, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; exact .inl ⟨h16, h256⟩
      simp only [hz, ↓reduceIte]; exact z₆ i h256
    · have k6 : s₆.mem (Stitch.pp s₀ + BitVec.ofNat 64 i) = s₅.mem (Stitch.pp s₀ + BitVec.ofNat 64 i) :=
        f₆ _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact notIn_base _ (by omega_arith) (by omega_arith)
      obtain nD : ∀ r ∈ [Stitch.dR s₀], ¬ r.Contains (Stitch.pp s₀ + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact notIn_p hp.base (by omega_arith) _ (by simp)
      obtain k4 : s₄.mem (Stitch.pp s₀ + BitVec.ofNat 64 i) = s₀.mem (Stitch.pp s₀ + BitVec.ofNat 64 i) := by
        rw [f₄ _ nD, f₁ _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact notIn_base _ (by omega_arith) (by omega_arith)]
      obtain b' := b₅ (i - 256) (by omega_arith)
      rw [show 256 + (i - 256) = i by omega_arith, k4] at b'
      rw [k6, b']
      obtain e' : (nb s₀ ≠ 16 * e ∧ (i - 256 < 128 ∨ 8 < nb s₀ - 16 * e)) ↔ zeroR (nb s₀) i = true := by
        simp only [zeroR, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega_arith
      by_cases hz : nb s₀ ≠ 16 * e ∧ (i - 256 < 128 ∨ 8 < nb s₀ - 16 * e)
      · simp only [hz, e'.mp hz, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
      · have hz' : zeroR (nb s₀) i = false := by
          cases h : zeroR (nb s₀) i
          · rfl
          · exact absurd (e'.mpr h) hz
        simp only [hz, hz', Bool.false_eq_true, ↓reduceIte]

/-- `decR`, and what it leaves in its working space (`zeroR`, as `encR`). -/
theorem decR_okL {s₀ : State} {np : Nat} (hp : SPrePrepared s₀ 1 np) (h8 : 8 ≤ np := by decide) :
    WP isa Impl.Gcm.X86_64.StitchR.decR s₀ fun s => DPost s₀ s ∧ Stitch.PieceL 512 zeroR s₀ s := by
  refine zeroTail_ok (Rdy := fun s => s.gpr = s₀.gpr ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr)
    (fun _ _ ⟨g, m, rd, wr⟩ g' _ m' rd' wr' => ⟨g'.trans g, m'.trans m, rd'.trans rd, wr'.trans wr⟩)
    (fun _ ⟨g, _⟩ => by rw [g]) (fun hlt s ⟨g, m, rd, wr⟩ => ?_) (fun h16 s ⟨g, m, rd, wr⟩ => ?_) ⟨rfl, rfl, rfl, rfl⟩
  · have hn : nb s = nb s₀ := by simp only [nb, g]
    exact WP.mono (decSmallC_okL (hp.congr g m rd wr) h8 (by rw [hn]; exact hp.base.nb16) (by rw [hn]; exact hlt))
      fun t ⟨ht, hl⟩ => ⟨ht.congr g m rd wr, hl.congr g m⟩
  · have hn : nb s = nb s₀ := by simp only [nb, g]
    exact WP.mono (decBig_okL ({ hp.congr g m rd wr with base := (hp.congr g m rd wr).base.ofLe (by rw [hn]; exact h16) }) h8)
      fun t ⟨ht, hl⟩ => ⟨ht.congr g m rd wr, hl.congr g m⟩

/-- `decR`: the decryption of any number of blocks from 1 on. -/
theorem decR_ok {s₀ : State} {np : Nat} (hp : SPrePrepared s₀ 1 np) (h8 : 8 ≤ np := by decide) :
    WP isa Impl.Gcm.X86_64.StitchR.decR s₀ (DPost s₀) :=
  WP.mono (decR_okL hp h8) fun _ h => h.1

/-- Both in-place loops, for a prepared key context, for any number of
blocks from 1 on. -/
theorem stitchR_okN (np : Nat) (hn : 8 ≤ np ∧ np ≤ 24 := by decide) (h8 : 8 ≤ np := by decide) :
    StitchOkM (CtxMode.preparedN np hn) Impl.Gcm.X86_64.StitchR.encR Impl.Gcm.X86_64.StitchR.decR 1 1 1 1 :=
  ⟨fun _ hp _ => encR_ok hp.toPrepared h8, fun _ hp _ => decR_ok hp.toPrepared h8⟩

theorem stitchR_ok :
    StitchOkM CtxMode.prepared Impl.Gcm.X86_64.StitchR.encR Impl.Gcm.X86_64.StitchR.decR 1 1 1 1 :=
  stitchR_okN 24

end VG.Proof.Gcm.X86_64.StitchR
