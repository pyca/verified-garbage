module

import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Dec
import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Ghash
public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareCT
public import VerifiedGarbage.Proof.Gcm.Poly
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Interleaved counter mode and GHASH: the powers and the field

The only module of `Proof/Gcm/X86_64/Stitch/` that computes in the field
(`Proof/Gcm/Poly.lean`), so that few modules import its algebra:

* `setupG_ok`: the setup computes `H'`–`H'¹⁶` (`x · H'ᵏ = Hᵏ`) as
  `vg_ghash_vpclmul` does (`Pclmul.hInv_ok`, `mul_ok`, `Vpclmul.powersYP_ok`,
  `powers16P_ok`); `setup_ok`: with the rest of the setup (`setupT_ok`), the
  state the loops start from (`Ready`), with those powers in the working
  space.
* `finE`, `finD`: with those powers, the two lanes' products of a body, in
  the order of an encryption or a decryption body, reduced and added, are
  `GHASH` over its sixteen blocks (`FinOk`).
* `stitch_ok`: both loops meet their contracts (`StitchOk`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce φ_reduce mul_ok const_ok ldrev_ok hInv_ok rev_eq Only)
open VG.Proof.Gcm.X86_64.Vpclmul (step16 powersYP_ok powers16P_ok)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (setupG setup ordE ordD enc dec)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Spec.Gcm (Block blockAt mul)

/-! ## The powers -/

/-- The powers from the key context at `rdi`, which the state may read. -/
theorem setupG_ok' {s₀ : State} (hk_in : InRegions (s₀.rd ++ s₀.wr) (kp s₀) 256) :
    WP isa (.block setupG) s₀ fun s =>
      (∀ l < 2, s.lane .xmm0 l = revMask) ∧ (∀ l < 2, s.lane .xmm1 l = poly) ∧
      (∀ k < 8, ∀ l < 2, x * φ (s.lane (preg16 k) l) = φ (hk s₀) ^ (16 - 2 * k - l)) ∧
      (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  simp only [setupG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s₀ (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .rdi 240 s₂ (by decide)
    (by rw [o₂.xmm _ (by decide), c₁, rev_eq])
    (by rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr _ (by decide)]; exact in_sub_int hk_in (by decide))) fun s₃ ⟨l₃, o₃⟩ => ?_
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

theorem setupG_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (.block setupG) s₀ fun s =>
      (∀ l < 2, s.lane .xmm0 l = revMask) ∧ (∀ l < 2, s.lane .xmm1 l = poly) ∧
      (∀ k < 8, ∀ l < 2, x * φ (s.lane (preg16 k) l) = φ (hk s₀) ^ (16 - 2 * k - l)) ∧
      (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr :=
  setupG_ok' hp.k_in

theorem setup_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (.block setup) s₀ fun s => ∃ P, Ready s₀ P s ∧
      ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ (hk s₀) ^ (16 - 2 * k - l) := by
  simp only [setup, List.append_assoc]
  rw [WP.block_append_iff]
  exact WP.mono (setupG_ok hp) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ =>
    WP.mono (setupT_ok hp l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR => ⟨_, hR, pw⟩

/-! ## The products of a body, in the field -/

/-- Sixteen blocks, in `Q`, the products in the order of a decryption body. -/
theorem step16D (H Y X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ X₁₀ X₁₁ X₁₂ X₁₃ X₁₄ X₁₅ T₁ T₂ T₃ T₄ T₅ T₆ T₇ T₈ T₉ T₁₀ T₁₁ T₁₂ T₁₃ T₁₄ T₁₅ T₁₆ : Block)
    (h₁ : x * φ T₁ = φ H) (h₂ : x * φ T₂ = φ H ^ 2) (h₃ : x * φ T₃ = φ H ^ 3) (h₄ : x * φ T₄ = φ H ^ 4) (h₅ : x * φ T₅ = φ H ^ 5) (h₆ : x * φ T₆ = φ H ^ 6) (h₇ : x * φ T₇ = φ H ^ 7) (h₈ : x * φ T₈ = φ H ^ 8) (h₉ : x * φ T₉ = φ H ^ 9) (h₁₀ : x * φ T₁₀ = φ H ^ 10) (h₁₁ : x * φ T₁₁ = φ H ^ 11) (h₁₂ : x * φ T₁₂ = φ H ^ 12) (h₁₃ : x * φ T₁₃ = φ H ^ 13) (h₁₄ : x * φ T₁₄ = φ H ^ 14) (h₁₅ : x * φ T₁₅ = φ H ^ 15) (h₁₆ : x * φ T₁₆ = φ H ^ 16) :
    reduce ((((((((Prod.zero.acc X₂ T₁₄).acc X₄ T₁₂).acc X₆ T₁₀).acc (Y ^^^ X₀) T₁₆).acc X₈ T₈).acc X₁₀ T₆).acc X₁₂ T₄).acc X₁₄ T₂) ^^^
        reduce ((((((((Prod.zero.acc X₃ T₁₃).acc X₅ T₁₁).acc X₇ T₉).acc X₁ T₁₅).acc X₉ T₇).acc X₁₁ T₅).acc X₁₃ T₃).acc X₁₅ T₁) =
      mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul ((Y ^^^ X₀)) H ^^^ X₁) H ^^^ X₂) H ^^^ X₃) H ^^^ X₄) H ^^^ X₅) H ^^^ X₆) H ^^^ X₇) H ^^^ X₈) H ^^^ X₉) H ^^^ X₁₀) H ^^^ X₁₁) H ^^^ X₁₂) H ^^^ X₁₃) H ^^^ X₁₄) H ^^^ X₁₅) H := by
  apply φ_inj
  simp only [φ_xor, φ_reduce, Prod.val_acc, Prod.val_zero, φ_mul]
  linear_combination (φ Y + φ X₀) * h₁₆ + φ X₁ * h₁₅ + φ X₂ * h₁₄ + φ X₃ * h₁₃ + φ X₄ * h₁₂ + φ X₅ * h₁₁ + φ X₆ * h₁₀ + φ X₇ * h₉ + φ X₈ * h₈ + φ X₉ * h₇ + φ X₁₀ * h₆ + φ X₁₁ * h₅ + φ X₁₂ * h₄ + φ X₁₃ * h₃ + φ X₁₄ * h₂ + φ X₁₅ * h₁

/-- The two lanes' products of an encryption body, reduced and added: `GHASH`
over the sixteen blocks. -/
theorem finE_mul (H : Block) (X : Nat → Block) (P : Nat → Nat → Block) (yl : Nat → Block) (hy1 : yl 1 = 0)
    (hP : ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ H ^ (16 - 2 * k - l)) :
    reduce (accN ordE X P yl 0 8) ^^^ reduce (accN ordE X P yl 1 8) =
      mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul ((yl 0 ^^^ X 0)) H ^^^ X 1) H ^^^ X 2) H ^^^ X 3) H ^^^ X 4) H ^^^ X 5) H ^^^ X 6) H ^^^ X 7) H ^^^ X 8) H ^^^ X 9) H ^^^ X 10) H ^^^ X 11) H ^^^ X 12) H ^^^ X 13) H ^^^ X 14) H ^^^ X 15) H := by
  have h₁ := hP 7 (by decide) 1 (by decide)
  rw [show 16 - 2 * 7 - 1 = 1 from rfl, pow_one] at h₁
  have h₂ := hP 7 (by decide) 0 (by decide)
  rw [show 16 - 2 * 7 - 0 = 2 from rfl] at h₂
  have h₃ := hP 6 (by decide) 1 (by decide)
  rw [show 16 - 2 * 6 - 1 = 3 from rfl] at h₃
  have h₄ := hP 6 (by decide) 0 (by decide)
  rw [show 16 - 2 * 6 - 0 = 4 from rfl] at h₄
  have h₅ := hP 5 (by decide) 1 (by decide)
  rw [show 16 - 2 * 5 - 1 = 5 from rfl] at h₅
  have h₆ := hP 5 (by decide) 0 (by decide)
  rw [show 16 - 2 * 5 - 0 = 6 from rfl] at h₆
  have h₇ := hP 4 (by decide) 1 (by decide)
  rw [show 16 - 2 * 4 - 1 = 7 from rfl] at h₇
  have h₈ := hP 4 (by decide) 0 (by decide)
  rw [show 16 - 2 * 4 - 0 = 8 from rfl] at h₈
  have h₉ := hP 3 (by decide) 1 (by decide)
  rw [show 16 - 2 * 3 - 1 = 9 from rfl] at h₉
  have h₁₀ := hP 3 (by decide) 0 (by decide)
  rw [show 16 - 2 * 3 - 0 = 10 from rfl] at h₁₀
  have h₁₁ := hP 2 (by decide) 1 (by decide)
  rw [show 16 - 2 * 2 - 1 = 11 from rfl] at h₁₁
  have h₁₂ := hP 2 (by decide) 0 (by decide)
  rw [show 16 - 2 * 2 - 0 = 12 from rfl] at h₁₂
  have h₁₃ := hP 1 (by decide) 1 (by decide)
  rw [show 16 - 2 * 1 - 1 = 13 from rfl] at h₁₃
  have h₁₄ := hP 1 (by decide) 0 (by decide)
  rw [show 16 - 2 * 1 - 0 = 14 from rfl] at h₁₄
  have h₁₅ := hP 0 (by decide) 1 (by decide)
  rw [show 16 - 2 * 0 - 1 = 15 from rfl] at h₁₅
  have h₁₆ := hP 0 (by decide) 0 (by decide)
  rw [show 16 - 2 * 0 - 0 = 16 from rfl] at h₁₆
  simp only [accN, List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil, ordE, inp, hy1, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero,
    Nat.zero_add, Nat.add_zero, zero_xor_b]
  exact step16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆

/-- The same for a decryption body. -/
theorem finD_mul (H : Block) (X : Nat → Block) (P : Nat → Nat → Block) (yl : Nat → Block) (hy1 : yl 1 = 0)
    (hP : ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ H ^ (16 - 2 * k - l)) :
    reduce (accN ordD X P yl 0 8) ^^^ reduce (accN ordD X P yl 1 8) =
      mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul ((yl 0 ^^^ X 0)) H ^^^ X 1) H ^^^ X 2) H ^^^ X 3) H ^^^ X 4) H ^^^ X 5) H ^^^ X 6) H ^^^ X 7) H ^^^ X 8) H ^^^ X 9) H ^^^ X 10) H ^^^ X 11) H ^^^ X 12) H ^^^ X 13) H ^^^ X 14) H ^^^ X 15) H := by
  have h₁ := hP 7 (by decide) 1 (by decide)
  rw [show 16 - 2 * 7 - 1 = 1 from rfl, pow_one] at h₁
  have h₂ := hP 7 (by decide) 0 (by decide)
  rw [show 16 - 2 * 7 - 0 = 2 from rfl] at h₂
  have h₃ := hP 6 (by decide) 1 (by decide)
  rw [show 16 - 2 * 6 - 1 = 3 from rfl] at h₃
  have h₄ := hP 6 (by decide) 0 (by decide)
  rw [show 16 - 2 * 6 - 0 = 4 from rfl] at h₄
  have h₅ := hP 5 (by decide) 1 (by decide)
  rw [show 16 - 2 * 5 - 1 = 5 from rfl] at h₅
  have h₆ := hP 5 (by decide) 0 (by decide)
  rw [show 16 - 2 * 5 - 0 = 6 from rfl] at h₆
  have h₇ := hP 4 (by decide) 1 (by decide)
  rw [show 16 - 2 * 4 - 1 = 7 from rfl] at h₇
  have h₈ := hP 4 (by decide) 0 (by decide)
  rw [show 16 - 2 * 4 - 0 = 8 from rfl] at h₈
  have h₉ := hP 3 (by decide) 1 (by decide)
  rw [show 16 - 2 * 3 - 1 = 9 from rfl] at h₉
  have h₁₀ := hP 3 (by decide) 0 (by decide)
  rw [show 16 - 2 * 3 - 0 = 10 from rfl] at h₁₀
  have h₁₁ := hP 2 (by decide) 1 (by decide)
  rw [show 16 - 2 * 2 - 1 = 11 from rfl] at h₁₁
  have h₁₂ := hP 2 (by decide) 0 (by decide)
  rw [show 16 - 2 * 2 - 0 = 12 from rfl] at h₁₂
  have h₁₃ := hP 1 (by decide) 1 (by decide)
  rw [show 16 - 2 * 1 - 1 = 13 from rfl] at h₁₃
  have h₁₄ := hP 1 (by decide) 0 (by decide)
  rw [show 16 - 2 * 1 - 0 = 14 from rfl] at h₁₄
  have h₁₅ := hP 0 (by decide) 1 (by decide)
  rw [show 16 - 2 * 0 - 1 = 15 from rfl] at h₁₅
  have h₁₆ := hP 0 (by decide) 0 (by decide)
  rw [show 16 - 2 * 0 - 0 = 16 from rfl] at h₁₆
  simp only [accN, List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil, ordD, inp, hy1, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero,
    Nat.zero_add, Nat.add_zero, zero_xor_b]
  exact step16D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆

/-- The products of an encryption body, for powers `x · Pₖₗ = H¹⁶⁻²ᵏ⁻ˡ`. -/
theorem finE {H : Block} {P : Nat → Nat → Block} (hP : ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ H ^ (16 - 2 * k - l)) :
    FinOk ordE H P := fun X yl hy1 => by
  rw [ghash16]; exact finE_mul H X P yl hy1 hP

/-- The products of a decryption body, for the same powers. -/
theorem finD {H : Block} {P : Nat → Nat → Block} (hP : ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ H ^ (16 - 2 * k - l)) :
    FinOk ordD H P := fun X yl hy1 => by
  rw [ghash16]; exact finD_mul H X P yl hy1 hP

/-! ## Both loops -/

/-- The encryption of `n` blocks (a multiple of 16, at least 16). -/
theorem enc_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) : WP isa enc s₀ (EPost s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨_, hR, hpw⟩ => encTail_ok hp hm (finE hpw) hR)

/-- The decryption of `n` blocks (a multiple of 16, at least 16). -/
theorem dec_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) : WP isa dec s₀ (DPost s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨_, hR, hpw⟩ => decTail_ok hp hm (finD hpw) hR)

/-- Both interleaved loops meet their contracts. -/
theorem stitch_ok : StitchOk Impl.Gcm.X86_64.Stitch.enc Impl.Gcm.X86_64.Stitch.dec := ⟨fun _ hp hm => enc_ok hp hm, fun _ hp hm => dec_ok hp hm⟩

end VG.Proof.Gcm.X86_64.Stitch

/-! # `vg_aes_gcm_prepare` on 256-bit registers

`times_ok`: a pass of `Prepare.times16` multiplies each of the eight pairs
of powers by `H'¹⁶`. `prepare_ok`: `setupG` computes `H'`–`H'¹⁶`
(`setupG_ok'`), stored as pairs 0–7, then twice multiplied by `H'¹⁶` and
stored as pairs 8–15 and 16–23; each lane `v` with `x · v = Hⁿ` is
`preparedPower (Hⁿ)` (`eq_prepared`). Here, with the field's other
module of the stitched loops, so that its algebra reaches no new module;
constant time is in `PrepareCT.lean`. -/

namespace VG.Proof.Gcm.X86_64.Prepare


open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Vpclmul (mulPair_ok pow_mul_pair)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16 mulPair)
open VG.Impl.Gcm.X86_64.Prepare (times16)
open VG.Spec.Gcm (Block hpow)

/-- The registers of the powers, and the products' scratch registers. -/
def wregs : List XReg := [.xmm8, .xmm9, .xmm10, .xmm11, .xmm3, .xmm4, .xmm5, .xmm6, .xmm15, .xmm14, .xmm13,
  .xmm12]

theorem preg16_lane : ∀ k < 8, laneSseBlock (mulPair (preg16 k) (preg16 k)) =
    some (Impl.Gcm.X86_64.Pclmul.mul (preg16 k) (preg16 k) .xmm7) := by decide

theorem preg16_ne : ∀ k < 8, preg16 k ≠ .xmm8 ∧ preg16 k ≠ .xmm9 ∧ preg16 k ≠ .xmm10 ∧ preg16 k ≠ .xmm11 := by
  decide

theorem preg16_inj : ∀ j < 8, ∀ k < 8, preg16 j = preg16 k → j = k := by decide

theorem preg16_wregs : ∀ k < 8, preg16 k ∈ wregs := by decide

/-- The first `n` multiplications of a pass: pairs `0`–`n - 1` times
`H'¹⁶`, which `ymm7` holds. -/
theorem times_ok {H : Block} {d : Nat} :
    ∀ n ≤ 8, ∀ s : State, (∀ l < 2, s.lane .xmm1 l = poly) → (∀ l < 2, x * φ (s.lane .xmm7 l) = φ H ^ 16) →
      (∀ k < 8, ∀ l < 2, x * φ (s.lane (preg16 k) l) = φ H ^ (16 - 2 * k - l + d)) →
      WP isa (.block ((List.range n).flatMap fun k => mulPair (preg16 k) (preg16 k))) s fun s' =>
        (∀ k < 8, ∀ l < 2, x * φ (s'.lane (preg16 k) l) =
          φ H ^ (16 - 2 * k - l + d + if k < n then 16 else 0)) ∧ YFrame wregs s s'
  | 0, _, s, _, _, hp => WP.block_nil ⟨fun k hk l hl => by simpa using hp k hk l hl, YFrame.refl _ _⟩
  | n + 1, hn, s, h1, h7, hp => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (times_ok n (by omega) s h1 h7 hp) fun t ⟨pt, ft⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    obtain ⟨n8, n9, n10, n11⟩ := preg16_ne n (by omega)
    have w1 : (.xmm1 : XReg) ∉ wregs := by decide
    have w7 : (.xmm7 : XReg) ∉ wregs := by decide
    refine WP.mono (mulPair_ok (preg16 n) (preg16 n) (preg16_lane n (by omega)) n8 n9 n10 n11 n8 n9 n10 n11 t
      (fun l hl => by rw [ft.lane _ w1 l hl]; exact h1 l hl)) fun t' ⟨m, f⟩ => ⟨fun k hk l hl => ?_, ?_⟩
    · by_cases hkn : k = n
      · subst hkn
        rw [ite_eq_left (by omega)]
        have e := pt k hk l hl
        rw [ite_eq_right (by omega)] at e
        rw [show 16 - 2 * k - l + d + 16 = (16 - 2 * k - l + d + 0) + 16 by omega]
        exact pow_mul_pair (m l hl) e (by rw [ft.lane _ w7 l hl]; exact h7 l hl)
      · have hne : preg16 k ≠ preg16 n := fun h => hkn (preg16_inj k hk n (by omega) h)
        rw [f.lane _ (by simp [hne, (preg16_ne k hk).1, (preg16_ne k hk).2.1, (preg16_ne k hk).2.2.1,
          (preg16_ne k hk).2.2.2]) l hl, pt k hk l hl]
        congr 2
        by_cases h : k < n
        · rw [ite_eq_left h, ite_eq_left (by omega)]
        · rw [ite_eq_right h, ite_eq_right (by omega)]
    · exact (ft.comp f).mono fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with hr | rfl | rfl | rfl | rfl | rfl
        · exact hr
        all_goals first | decide | exact preg16_wregs n (by omega)

/-- A pass: each pair times `H'¹⁶`. -/
theorem times16_ok {H : Block} {d : Nat} (s : State) (h1 : ∀ l < 2, s.lane .xmm1 l = poly)
    (h7 : ∀ l < 2, x * φ (s.lane .xmm7 l) = φ H ^ 16)
    (hp : ∀ k < 8, ∀ l < 2, x * φ (s.lane (preg16 k) l) = φ H ^ (16 - 2 * k - l + d)) :
    WP isa (.block times16) s fun s' =>
      (∀ k < 8, ∀ l < 2, x * φ (s'.lane (preg16 k) l) = φ H ^ (16 - 2 * k - l + (d + 16))) ∧
      YFrame wregs s s' :=
  WP.mono (times_ok 8 (Nat.le_refl _) s h1 h7 hp) fun _ ⟨p, f⟩ =>
    ⟨fun k hk l hl => by rw [p k hk l hl, ite_eq_left hk, Nat.add_assoc], f⟩

open VG.Proof.Gcm.X86_64.Stitch (setupG_ok' storesK_ok in_sub_int)
open VG.Proof.Gcm.X86_64.Vpclmul (vinsB_ok)
open VG.Impl.Gcm.X86_64.Stitch (setupG storesK pregs)
open VG.Impl.Gcm.X86_64.Prepare (prepare)
open VG.Proof.Gcm.X86_64.Pclmul (eq_prepared)

theorem pregs_rev : ∀ i (h : i < pregs.reverse.length), pregs.reverse[i] = preg16 (7 - i)
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
  | 7, _ => rfl | _ + 8, h => absurd h (by simp [pregs])

theorem pregs_rev_length : pregs.reverse.length = 8 := rfl

/-- Pairs `j`–`j + 7` stored from the registers of the powers, as
`H^(2 (j + i) + 2 - l)`, prepared. -/
theorem stored {H : Block} {C : Addr} {s s' : State} {j d : Nat} (hd : d = 2 * (j - 8)) (hj : 8 ≤ j)
    (sv : ∀ k (h : k < pregs.reverse.length), ∀ l < 2,
      s'.mem.readW (C + BitVec.ofNat 64 (32 * (j + k) + 16 * l)) 128 = s.lane pregs.reverse[k] l)
    (pw : ∀ k < 8, ∀ l < 2, x * φ (s.lane (preg16 k) l) = φ H ^ (16 - 2 * k - l + d)) :
    ∀ i < 8, ∀ l < 2, s'.mem.readW (C + BitVec.ofNat 64 (256 + 32 * (j - 8 + i) + 16 * l)) 128 =
      Spec.Gcm.preparedPower (hpow H (2 * (j - 8 + i) + 2 - l)) := fun i hi l hl => by
  have h := sv i (by rw [pregs_rev_length]; exact hi) l hl
  rw [pregs_rev i (by rw [pregs_rev_length]; exact hi),
    show 32 * (j + i) + 16 * l = 256 + 32 * (j - 8 + i) + 16 * l by omega] at h
  rw [h]
  exact eq_prepared (by rw [pw (7 - i) (by omega) l hl]; congr 1; omega)

/-- `vzeroupper` keeps all but the vector registers. -/
theorem vzu_ok (s : State) :
    WP isa (.block [.vop .vzeroupper]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [WP.block_cons_iff]; exact ⟨_, rfl, WP.block_nil ⟨rfl, rfl, rfl, rfl⟩⟩

/-- `prepare`: the 48 prepared powers of the hash subkey at `C + 240` into
pairs 0–23 of the context at `C`, nothing else written. -/
theorem prepare_ok {s₀ : State} (hw : InRegions s₀.wr (s₀.gpr .rdi) 1024)
    (hwrap : (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64) :
    WP isa prepare s₀ (PrepOk s₀) := by
  set C := s₀.gpr .rdi with hC
  set H := Spec.Gcm.ctxH s₀.mem C with hH
  have hk : InRegions (s₀.rd ++ s₀.wr) C 256 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, by simp only [Region.Contains] at hc ⊢; omega⟩
  simp only [prepare, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (setupG_ok' hk) fun s₁ ⟨_, l1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  have r₁ : s₁.gpr .rdi = C := g₁ _ (by decide)
  have win : ∀ (t : State), t.wr = s₀.wr → t.gpr .rdi = C → ∀ j, j + 8 ≤ 32 →
      ∀ k < pregs.reverse.length, InRegions t.wr (t.gpr .rdi + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32 :=
    fun t ht hr j hj k hk' => by
      rw [ht, hr]; exact in_sub_int hw (by rw [pregs_rev_length] at hk'; omega)
  have wwrap : ∀ (t : State), t.gpr .rdi = C → ∀ j, j + 8 ≤ 32 →
      (t.gpr .rdi).toNat + 32 * (j + pregs.reverse.length) ≤ 2 ^ 64 :=
    fun t hr j hj => by
      rw [hr, pregs_rev_length]; exact Nat.le_trans (Nat.add_le_add_left (by omega) _) hwrap
  -- Pairs 0–7.
  rw [WP.block_append_iff]
  refine WP.mono (storesK_ok .rdi pregs.reverse 8 s₁ (win s₁ (by rw [wr₁]) r₁ 8 (by decide))
    (wwrap s₁ r₁ 8 (by decide))) fun s₂ ⟨sv₂, fr₂, g₂, rd₂, wr₂, ln₂⟩ => ?_
  rw [r₁] at sv₂ fr₂
  have pw₂ : ∀ k < 8, ∀ l < 2, x * φ (s₂.lane (preg16 k) l) = φ H ^ (16 - 2 * k - l + 0) := fun k hk l hl => by
    rw [ln₂, pw k hk l hl, Nat.add_zero]; rfl
  have P0 := stored (j := 8) (d := 0) rfl (by decide) sv₂ (fun k hk l hl => by rw [← ln₂]; exact pw₂ k hk l hl)
  -- `H'¹⁶` in both lanes of `ymm7`.
  rw [WP.block_append_iff]
  refine WP.mono (vinsB_ok .xmm3 s₂) fun s₃ ⟨b₃, f₃⟩ => ?_
  have h7₃ : ∀ l < 2, x * φ (s₃.lane .xmm7 l) = φ H ^ 16 := fun l hl => by
    rw [b₃ l hl]; exact pw₂ 0 (by decide) 0 (by decide)
  have h1₃ : ∀ l < 2, s₃.lane .xmm1 l = poly := fun l hl => by
    rw [f₃.lane _ (by decide) l hl, ln₂]; exact l1 l hl
  have pw₃ : ∀ k < 8, ∀ l < 2, x * φ (s₃.lane (preg16 k) l) = φ H ^ (16 - 2 * k - l + 0) := fun k hk l hl => by
    rw [f₃.lane _ (by have := preg16_wregs k hk; revert this; generalize preg16 k = r; intro h; simp only [wregs,
      List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> decide) l hl]
    exact pw₂ k hk l hl
  -- Pairs 8–15.
  rw [WP.block_append_iff]
  refine WP.mono (times16_ok s₃ h1₃ h7₃ pw₃) fun s₄ ⟨pw₄, f₄⟩ => ?_
  have e₄ : s₄.gpr .rdi = C := by rw [f₄.gpr, f₃.gpr, g₂, r₁]
  have wr₄ : s₄.wr = s₀.wr := by rw [f₄.wr, f₃.wr, wr₂, wr₁]
  rw [WP.block_append_iff]
  refine WP.mono (storesK_ok .rdi pregs.reverse 16 s₄ (win s₄ wr₄ e₄ 16 (by decide)) (wwrap s₄ e₄ 16 (by decide)))
    fun s₅ ⟨sv₅, fr₅, g₅, rd₅, wr₅, ln₅⟩ => ?_
  rw [e₄] at sv₅ fr₅
  have P1 := stored (j := 16) (d := 16) rfl (by decide) sv₅ (fun k hk l hl => pw₄ k hk l hl)
  -- Pairs 16–23.
  have w7 : (.xmm7 : XReg) ∉ wregs := by decide
  have w1 : (.xmm1 : XReg) ∉ wregs := by decide
  rw [WP.block_append_iff]
  refine WP.mono (times16_ok (H := H) (d := 16) s₅ (fun l hl => by rw [ln₅, f₄.lane _ w1 l hl]; exact h1₃ l hl)
    (fun l hl => by rw [ln₅, f₄.lane _ w7 l hl]; exact h7₃ l hl)
    (fun k hk l hl => by rw [ln₅]; exact pw₄ k hk l hl)) fun s₆ ⟨pw₆, f₆⟩ => ?_
  have e₆ : s₆.gpr .rdi = C := by rw [f₆.gpr, g₅, e₄]
  have wr₆ : s₆.wr = s₀.wr := by rw [f₆.wr, wr₅, wr₄]
  rw [WP.block_append_iff]
  refine WP.mono (storesK_ok .rdi pregs.reverse 24 s₆ (win s₆ wr₆ e₆ 24 (by decide)) (wwrap s₆ e₆ 24 (by decide)))
    fun s₇ ⟨sv₇, fr₇, g₇, rd₇, wr₇, _⟩ => ?_
  rw [e₆] at sv₇ fr₇
  have P2 := stored (j := 24) (d := 32) rfl (by decide) sv₇ (fun k hk l hl => pw₆ k hk l hl)
  refine WP.mono (vzu_ok s₇) fun s ⟨g, m, rd, wr⟩ => ⟨fun k hk l hl => ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · -- Each pair from its pass, kept by the later stores.
    have keep : ∀ {a : Nat} {t t' : State}, Frame [⟨C + BitVec.ofNat 64 a, 256⟩] t.mem t'.mem →
        256 + 32 * k + 16 * l + 16 ≤ a ∨ a + 256 ≤ 256 + 32 * k + 16 * l → a + 256 ≤ 1024 →
        t'.mem.readW (C + BitVec.ofNat 64 (256 + 32 * k + 16 * l)) 128 =
          t.mem.readW (C + BitVec.ofNat 64 (256 + 32 * k + 16 * l)) 128 := fun f h ha =>
      f.readW (Region.contains_self _ _) (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact Offset.disjoint C (by omega) (by omega) (by omega)) (by decide)
    have m₄ : s₄.mem = s₂.mem := by rw [f₄.mem, f₃.mem]
    have m₆ : s₆.mem = s₅.mem := f₆.mem
    rw [m]
    rcases (by omega : k < 8 ∨ (8 ≤ k ∧ k < 16) ∨ 16 ≤ k) with h | ⟨h, h'⟩ | h
    · rw [keep (t := s₆) (a := 768) fr₇ (by omega) (by decide), m₆,
        keep (t := s₄) (a := 512) fr₅ (by omega) (by decide), m₄]
      have := P0 k h l hl
      rw [show 8 - 8 + k = k by omega] at this
      exact this
    · rw [keep (t := s₆) (a := 768) fr₇ (by omega) (by decide)]
      have := P1 (k - 8) (by omega) l hl
      rw [show 16 - 8 + (k - 8) = k by omega] at this
      rw [m₆]; exact this
    · have := P2 (k - 16) (by omega) l hl
      rw [show 24 - 8 + (k - 16) = k by omega] at this
      exact this
  · rw [m]
    have sub : ∀ {a : Nat}, a + 256 ≤ 1024 → 256 ≤ a → ∀ r ∈ [(⟨C + BitVec.ofNat 64 a, 256⟩ : Region)],
        ∃ r' ∈ [(⟨C + BitVec.ofNat 64 256, 768⟩ : Region)], Region.Sub r r' := fun h h' r hr =>
      ⟨_, List.mem_singleton_self _, by obtain rfl := List.mem_singleton.mp hr; exact Offset.sub C h' (by omega)⟩
    rw [← m₁]
    exact (((fr₂.sub (sub (by decide) (by decide))).trans (by rw [f₄.mem, f₃.mem]; exact Frame.refl _ _)).trans
      (fr₅.sub (sub (by decide) (by decide)))).trans (by rw [← f₆.mem]; exact (fr₇.sub (sub (by decide) (by decide))))
  · rw [g, g₇, f₆.gpr, g₅, f₄.gpr, f₃.gpr, g₂, g₁ r hr]
  · rw [rd, rd₇, f₆.rd, rd₅, f₄.rd, f₃.rd, rd₂, rd₁]
  · rw [wr, wr₇, wr₆]

theorem prepare_verified : Verified X86_64.target prepare (Spec.Gcm.prepareContract X86_64.abi) :=
  verified_of prepare (fun _ hw hwrap => prepare_ok hw hwrap) (by decide +kernel) prepare_ct

end VG.Proof.Gcm.X86_64.Prepare
