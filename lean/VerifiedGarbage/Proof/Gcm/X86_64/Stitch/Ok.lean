module

import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Dec
import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Ghash
public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareCT
public import VerifiedGarbage.Proof.Gcm.Poly
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

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

/-! # Storing `setupG`'s powers as prepared pairs

`stored`: the pairs `storesK` writes from the registers of `setupG`'s powers
(`setupG_ok'`) are the prepared powers (`eq_prepared`), which
`vg_aes_gcm_prepare16` here and `vg_aes_gcm_prepare_vpclmul_avx512`
(`PrepareZ.lean`) store. Here, with the field's other module of the stitched
loops, so that its algebra reaches no new module. -/

namespace VG.Proof.Gcm.X86_64.Prepare


open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Spec.Gcm (Block hpow)

open VG.Proof.Gcm.X86_64.Stitch (setupG_ok' storesK_ok in_sub_int)
open VG.Impl.Gcm.X86_64.Stitch (setupG storesK pregs)
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

end VG.Proof.Gcm.X86_64.Prepare

/-! # `vg_aes_gcm_prepare16` on 256-bit registers

`prepare16_ok`: `setupG` computes `H'`–`H'¹⁶`, which are stored as pairs 0–7
of the context (`stored`), and nothing else is written;
`prepare16_verified`: `Spec.Gcm.prepare16Contract`, with the constant time
of `PrepareCT.lean`. Here, with `stored`, so that the field's algebra reaches
no new module. -/

namespace VG.Proof.Gcm.X86_64.Prepare16

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Prepare16 (prepare16)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Impl.Gcm.X86_64.Stitch (setupG storesK pregs)
open VG.Proof.Gcm.X86_64.Stitch (setupG_ok' storesK_ok in_sub_int)
open VG.Proof.Gcm.X86_64.Prepare (stored vzu_ok pregs_rev_length bytesAt_frame satState)

/-- What `vg_aes_gcm_prepare16` does from `s₀`: the 16 prepared powers of the
hash subkey at `C + 240` into pairs 0–7 of the context at `C`, nothing else
written, and the registers but `rax` kept. -/
def PrepOk16 (s₀ s : State) : Prop :=
  (∀ k < 8, ∀ l < 2, s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (256 + 32 * k + 16 * l)) 128 =
    Spec.Gcm.preparedPower (Spec.Gcm.hpow (Spec.Gcm.ctxH s₀.mem (s₀.gpr .rdi)) (2 * k + 2 - l))) ∧
  Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 256, 256⟩] s₀.mem s.mem ∧
  (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

/-- `prepare16`: the 16 prepared powers of the hash subkey at `C + 240` into
pairs 0–7 of the context at `C`, nothing else written. -/
theorem prepare16_ok {s₀ : State} (hw : InRegions s₀.wr (s₀.gpr .rdi) 1024)
    (hwrap : (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64) :
    WP isa prepare16 s₀ (PrepOk16 s₀) := by
  set C := s₀.gpr .rdi with hC
  set H := Spec.Gcm.ctxH s₀.mem C with hH
  have hk : InRegions (s₀.rd ++ s₀.wr) C 256 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, by simp only [Region.Contains] at hc ⊢; omega⟩
  simp only [prepare16, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (setupG_ok' hk) fun s₁ ⟨_, _, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  have r₁ : s₁.gpr .rdi = C := g₁ _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storesK_ok .rdi pregs.reverse 8 s₁
    (fun k hk' => by rw [wr₁, r₁]; exact in_sub_int hw (by rw [pregs_rev_length] at hk'; omega))
    (by rw [r₁, pregs_rev_length]; exact Nat.le_trans (by omega) hwrap))
    fun s₂ ⟨sv₂, fr₂, g₂, rd₂, wr₂, ln₂⟩ => ?_
  rw [r₁] at sv₂ fr₂
  have P0 := stored (H := H) (j := 8) (d := 0) rfl (by decide) sv₂ (fun k hk l hl => by
    rw [pw k hk l hl, Nat.add_zero]; rfl)
  refine WP.mono (vzu_ok s₂) fun s ⟨g, m, rd, wr⟩ => ⟨fun k hk l hl => ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [m]
    have := P0 k hk l hl
    rw [show 8 - 8 + k = k by omega] at this
    exact this
  · rw [m, ← m₁]; exact fr₂
  · rw [g, g₂, g₁ r hr]
  · rw [rd, rd₂, rd₁]
  · rw [wr, wr₂, wr₁]

theorem correct16 {s₀ : State} (hp : prepare16X86_64.pre s₀) :
    WP isa prepare16 s₀ fun s => gprPreserved s₀ s ∧ prepare16X86_64.post s₀ s := by
  obtain ⟨_, hwr, hwrap, hret⟩ := hp
  have hw : InRegions s₀.wr (s₀.gpr .rdi) 1024 := by
    rw [hwr]; exact ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (prepare16_ok hw hwrap) fun s ⟨pw, fr, g, _, _⟩ => ?_
  have keep : Spec.Aes.bytesAt s.mem (s₀.gpr .rdi) 256 = Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) 256 :=
    bytesAt_frame fr (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.base_disjoint _ (by decide) (by omega)) (by decide)
  have hH : Spec.Gcm.ctxH s.mem (s₀.gpr .rdi) = Spec.Gcm.ctxH s₀.mem (s₀.gpr .rdi) := by
    simp only [Spec.Gcm.ctxH, Spec.Gcm.blockAt]
    rw [bytesAt_frame fr (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (Offset.disjoint (s₀.gpr .rdi) (d := 240) (n := 16) (e := 256) (k := 256) (.inl (by decide)) (by decide)
        (by omega)).sub_left (Region.sub_prefix (Nat.le_refl _))) (by decide)]
  refine ⟨⟨fun r hr => g r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ?_⟩, keep, fun k hk => ?_⟩
  · exact fr.readW (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hret.sub_right (Offset.sub_base (s₀.gpr .rdi) (by decide))) (by decide)
  · rw [hH]
    have p0 := pw k hk 0 (by decide)
    have p1 := pw k hk 1 (by decide)
    rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at p0
    rw [show 256 + 32 * k + 16 * 1 = 272 + 32 * k by omega, show 2 * k + 2 - 1 = 2 * k + 1 by omega] at p1
    exact ⟨p0, p1⟩

theorem prepare16_correct (s : State) (hs : prepare16X86_64.pre s) :
    ∃ t s', Exec isa prepare16 s t s' ∧ abiPreserved s s' ∧ prepare16X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct16 hs
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem prepare16_verified :
    Verified X86_64.target prepare16 (Spec.Gcm.prepare16Contract X86_64.abi) :=
  Verified.of_correct prepare16_correct prepare16_ct (by
    sig_implies [Spec.Gcm.prepare16Contract, Spec.Gcm.prepareSig, Spec.Gcm.prepare16Post, prepare16X86_64,
      X86_64.abi, X86_64.argRegs] [satState] using satState)

end VG.Proof.Gcm.X86_64.Prepare16
