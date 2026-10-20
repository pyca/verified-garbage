module

import VerifiedGarbage.Proof.Bignum.AArch64.Csub
public import VerifiedGarbage.Impl.Bignum.AArch64.R2Div
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `R² mod m` by long division on AArch64: the subtraction

`subPass` replaces the `w + 1` low words `P` of the accumulator by
`t = x 2^64 - P` modulo `2^(64 (w + 1))`, `x` the `w` words at `x11`:
`t + P = x 2^64 + 2^(64 (w + 1)) b` for the borrow `b` (`subPass_ok`).
`addBack` adds `m` to the `w + 1` words `t` if `t ≥ 2^(64 (w + 1)) / 2`
(its sign, in two's complement): `t' + 2^(64 (w + 1)) c = t + m` for the
carry `c` (`r2dAddBack_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.R2Div VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- A word of a subtraction from `X 2^64`: `r + y + !c = x + 2^64 !c'`. -/
theorem subP_arith {A M X Q r y x ci co : Nat} (h : A + M = 2 ^ 64 * X + Q * 2 ^ 64 * ci)
    (hs : r + y + ci = x + 2 ^ 64 * co) :
    A + Q * 2 ^ 64 * r + (M + Q * 2 ^ 64 * y) = 2 ^ 64 * (X + Q * x) + Q * 2 ^ 64 * 2 ^ 64 * co := by
  have e : A + Q * 2 ^ 64 * r + (M + Q * 2 ^ 64 * y) = (A + M) + Q * 2 ^ 64 * (r + y) := by
    rw [Nat.mul_add]; omega
  rw [e, h, Nat.add_assoc, ← Nat.mul_add, Nat.add_comm ci, hs, Nat.mul_add, Nat.mul_add]
  ac_rfl

/-- After `j` words of `subPass`'s loop, from the memory `m₀` and the state
`s₀` after its first word. -/
structure SubPInv (m₀ : Mem) (s₀ : State) (B : Addr) (Z eA eX : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eA + 8 * (j + 1))
  x17 : t.gpr .x17 = off B (eX + 8 * j)
  out : Outside B eA (8 * (j + 1)) m₀ t.mem
  val : wv t.mem B eA (j + 1) + wv m₀ B eA (j + 1) = 2 ^ 64 * wv m₀ B eX j + 2 ^ (64 * (j + 1)) * (!t.c).toNat

theorem subPStep_ok {m₀ : Mem} {s₀ : State} {B : Addr} {Z w eA eX : Nat}
    (hA : eA + 8 * (w + 1) ≤ Z) (hX : eX + 8 * w ≤ Z)
    (sX : eA + 8 * (w + 1) ≤ eX ∨ eX + 8 * w ≤ eA) {j : Nat} (hj : j < w)
    {t : State} (hI : SubPInv m₀ s₀ B Z eA eX j t) :
    WP isa (.block ([ld .x4 .x17, ld .x3 .x16, .sbcs .x .x3 .x4 .x3, st .x3 .x16, next .x16, next .x17] ++
        ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      SubPInv m₀ s₀ B Z eA eX (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eA + 8 * (j + 1))) (word t.mem B (eX + 8 * j) +
        ~~~word t.mem B (eA + 8 * (j + 1)) + BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (eX + 8 * j)).toNat + (~~~word t.mem B (eA + 8 * (j + 1))).toNat +
        t.c.toNat) ∧
      t₁.gpr .x16 = off B (eA + 8 * (j + 1) + 8) ∧ t₁.gpr .x17 = off B (eX + 8 * j + 8))
    (by brun [hI.x16, hI.x17, hI.scr.ld (show eA + 8 * (j + 1) + 8 ≤ Z by omega),
      hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega), hI.scr.st (show eA + 8 * (j + 1) + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hx : word t.mem B (eX + 8 * j) = word m₀ B (eX + 8 * j) :=
    hI.out.word (d := eX + 8 * j) (by omega) (by omega)
  have hy : word t.mem B (eA + 8 * (j + 1)) = word m₀ B (eA + 8 * (j + 1)) :=
    hI.out.word (d := eA + 8 * (j + 1)) (Or.inr (Nat.le_refl _)) (by omega)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.add_assoc, ← Nat.mul_succ],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    exact fun x hx' => (writeW_outside t.mem B _ (by omega) x (by omega)).trans (hI.out x (by omega))
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hc', hc]
    have hs := sbcs_toNat (word t.mem B (eX + 8 * j)) (word t.mem B (eA + 8 * (j + 1))) t.c
    rw [hx, hy] at hs ⊢
    have hval := hI.val
    rw [pow64_succ j] at hval ⊢
    rw [show j + 1 + 1 = (j + 1) + 1 from rfl, wv, wv, pow64_succ (j + 1), pow64_succ j]
    exact subP_arith hval hs

/-- `subPass`: the `w + 1` low words `P` of the accumulator (at `x8`) become
`t = x 2^64 - P` modulo `2^(64 (w + 1))` for the `w` words `x` at `x11`. -/
theorem subPass_ok {s : State} {B : Addr} {Z w eA eX : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .x8 = off B eA) (h11 : s.gpr .x11 = off B eX) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : s.gpr .x7 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hA : eA + 8 * (w + 1) ≤ Z) (hX : eX + 8 * w ≤ Z) (sX : eA + 8 * (w + 1) ≤ eX ∨ eX + 8 * w ≤ eA) :
    WP isa subPass s fun t => ∃ b : Bool,
      wv t.mem B eA (w + 1) + wv s.mem B eA (w + 1) = 2 ^ 64 * wv s.mem B eX w + 2 ^ (64 * (w + 1)) * b.toNat ∧
      Outside B eA (8 * (w + 1)) s.mem t.mem ∧ Keep [.x3, .x4, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  unfold subPass
  refine WP.seq (WP.mono (WP.keep [.x3, .x14, .x16, .x17] (Q := fun t =>
    t.gpr .x16 = off B (eA + 8) ∧ t.gpr .x17 = off B eX ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧
    t.mem = s.mem.writeW (off B eA) (0 + ~~~word s.mem B eA + BitVec.ofNat 64 (true : Bool).toNat) ∧
    t.c = decide (2 ^ 64 ≤ (0 : BitVec 64).toNat + (~~~word s.mem B eA).toNat + (true : Bool).toNat))
    (by brun [h8, h11, h12, h7, hs.ld (show eA + 8 ≤ Z by omega), hs.st (show eA + 8 ≤ Z by omega)]
        <;> rfl) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h16, h17, h14, hm₁, hc₁⟩, k₁⟩ => ?_)
  have h0 : SubPInv s.mem s₁ B Z eA eX 0 s₁ := by
    refine ⟨hs.congr k₁.wr, Keep.refl _ _, by rw [h16], by rw [h17]; rfl, ?_, ?_⟩
    · rw [hm₁]
      exact fun x hx' => writeW_outside s.mem B (d := eA) _ (by omega) x (by omega)
    · have e := sbcs_toNat 0 (word s.mem B eA) true
      rw [hm₁, hc₁]
      have := wv_writeW_top s.mem B eA 0 (0 + ~~~word s.mem B eA + BitVec.ofNat 64 (true : Bool).toNat)
        (by omega)
      simp only [Nat.mul_zero, Nat.add_zero] at this
      rw [this]
      simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add] at e ⊢
      rw [show (BitVec.toNat (0 : BitVec 64)) = 0 from rfl] at e
      simp only [Bool.not_true, Bool.toNat_false, Nat.add_zero, Nat.zero_add] at e ⊢
      rw [show (BitVec.toNat (0 : BitVec 64)) = 0 from rfl, Nat.zero_add]
      omega
  refine WP.mono (wp_countdown (N := w) (by omega) (by omega) (SubPInv s.mem s₁ B Z eA eX)
    (fun j hj t hI _ => subPStep_ok hA hX sX hj hI) h0 h14) fun t hI => ?_
  exact ⟨!t.c, hI.val, hI.out, (k₁.trans hI.keep).mono (by decide)⟩

/-! ## `R - m` -/

/-- After `j` words of `neg`'s loop: `x_j + m_j = 2^(64 j) b` for the borrow `b`. -/
structure R2dNegInv (m₀ : Mem) (s₀ : State) (B : Addr) (Z eX eM : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eX + 8 * j)
  x17 : t.gpr .x17 = off B (eM + 8 * j)
  out : Outside B eX (8 * j) m₀ t.mem
  val : wv t.mem B eX j + wv m₀ B eM j = 2 ^ (64 * j) * (!t.c).toNat

theorem r2dNegStep_ok {m₀ : Mem} {s₀ : State} {B : Addr} {Z w eX eM : Nat} (h7 : s₀.gpr .x7 = 0)
    (hX : eX + 8 * w ≤ Z) (hM : eM + 8 * w ≤ Z) (sM : eX + 8 * w ≤ eM ∨ eM + 8 * w ≤ eX) {j : Nat} (hj : j < w)
    {t : State} (hI : R2dNegInv m₀ s₀ B Z eX eM j t) :
    WP isa (.block ([ld .x4 .x17, .sbcs .x .x3 .x7 .x4, st .x3 .x16, next .x16, next .x17] ++
        ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      R2dNegInv m₀ s₀ B Z eX eM (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eX + 8 * j)) (0 + ~~~word t.mem B (eM + 8 * j) + BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (0 : BitVec 64).toNat + (~~~word t.mem B (eM + 8 * j)).toNat + t.c.toNat) ∧
      t₁.gpr .x16 = off B (eX + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eM + 8 * j + 8))
    (by brun [hI.x16, hI.x17, t7, hI.scr.ld (show eM + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show eX + 8 * j + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hy : word t.mem B (eM + 8 * j) = word m₀ B (eM + 8 * j) :=
    hI.out.word (d := eM + 8 * j) (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    exact fun x hx' => (writeW_outside t.mem B _ (by omega) x (by omega)).trans (hI.out x (by omega))
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hc', hc]
    have hs := sbcs_toNat 0 (word t.mem B (eM + 8 * j)) t.c
    rw [hy] at hs ⊢
    have hval := hI.val
    rw [wv, pow64_succ]
    simp only [show (BitVec.toNat (0 : BitVec 64)) = 0 from rfl, Nat.zero_add] at hs ⊢
    generalize (0 + ~~~word m₀ B (eM + 8 * j) + BitVec.ofNat 64 t.c.toNat).toNat = r at hs ⊢
    generalize 2 ^ (64 * j) = P at hval ⊢
    have e : wv t.mem B eX j + P * r + (wv m₀ B eM j + P * (word m₀ B (eM + 8 * j)).toNat) =
        (wv t.mem B eX j + wv m₀ B eM j) + P * (r + (word m₀ B (eM + 8 * j)).toNat) := by
      rw [Nat.mul_add]; omega
    rw [e, hval, ← Nat.mul_add, Nat.mul_assoc]
    exact congrArg (P * ·) (by omega)

/-- `neg`: `x := R - m` over `w` words (`x` at `x11`, `m` at `x9`):
`x + m = 2^(64 w) b` for the borrow `b`. -/
theorem r2dNeg_ok {s : State} {B : Addr} {Z w eX eM : Nat} (hs : Scr s B Z)
    (h11 : s.gpr .x11 = off B eX) (h9 : s.gpr .x9 = off B eM) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : s.gpr .x7 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hX : eX + 8 * w ≤ Z) (hM : eM + 8 * w ≤ Z) (sM : eX + 8 * w ≤ eM ∨ eM + 8 * w ≤ eX) :
    WP isa neg s fun t => ∃ b : Bool,
      wv t.mem B eX w + wv s.mem B eM w = 2 ^ (64 * w) * b.toNat ∧
      Outside B eX (8 * w) s.mem t.mem ∧ Keep [.x3, .x4, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  unfold neg
  refine WP.seq (WP.mono (WP.keep [.x3, .x14, .x16, .x17] (Q := fun t =>
    t.gpr .x16 = off B eX ∧ t.gpr .x17 = off B eM ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = true ∧ t.mem = s.mem)
    (by brun [h11, h9, h12, h7]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h16, h17, h14, hc₁, hm₁⟩, k₁⟩ => ?_)
  have h0 : R2dNegInv s.mem s₁ B Z eX eM 0 s₁ :=
    ⟨hs.congr k₁.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, by rw [hm₁]; exact Outside.refl _ _ _ _,
      by rw [hc₁]; rfl⟩
  refine WP.mono (wp_countdown (N := w) (by omega) (by omega) (R2dNegInv s.mem s₁ B Z eX eM)
    (fun j hj t hI _ => r2dNegStep_ok ((k₁.gpr .x7 (by decide)).trans h7) hX hM sM hj hI) h0 h14) fun t hI => ?_
  exact ⟨!t.c, hI.val, hI.out, (k₁.trans hI.keep).mono (by decide)⟩

/-! ## Adding `m` back -/

/-- `adcs`, as numbers. -/
theorem adcs_val (a b : BitVec 64) (c : Bool) :
    (a + b + BitVec.ofNat 64 c.toNat).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)).toNat =
      a.toNat + b.toNat + c.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hc1 := Bool.toNat_le c
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c.toNat < 2 ^ 64)]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

/-- The mask of the top bit of `v`: `0 - (v >>> 63)`. -/
theorem sign_mask (v : BitVec 64) : 0 - v >>> 63 = mask (decide (2 ^ 63 ≤ v.toNat)) := by
  have hv := v.isLt
  have e : v >>> 63 = (BitVec.ofBool (decide (2 ^ 63 ≤ v.toNat))).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    by_cases h : 2 ^ 63 ≤ v.toNat <;> simp only [h, decide_true, decide_false] <;>
      (show _ = BitVec.toNat (BitVec.setWidth 64 (BitVec.ofBool _)); simp) <;> omega
  rw [e]; rfl

/-- `(w <<< 3)` is `8 w`. -/
theorem r2d_ofNat_shl3 {w : Nat} (hw : w < 2 ^ 61) : BitVec.ofNat 64 w <<< 3 = BitVec.ofNat 64 (8 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega : w < 2 ^ 64)]
  omega

/-- The sign of a number of `w + 1` words is its top word's top bit. -/
theorem sign_top (m : Mem) (B : Addr) (eA w : Nat) :
    decide (2 ^ 63 ≤ (word m B (eA + 8 * w)).toNat) = decide (2 ^ (64 * (w + 1)) / 2 ≤ wv m B eA (w + 1)) := by
  have hP : 2 ^ (64 * (w + 1)) / 2 = 2 ^ (64 * w) * 2 ^ 63 := by
    rw [pow64_succ, show (2 : Nat) ^ 64 = 2 ^ 63 * 2 from rfl, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide)]
  have hl := wv_lt m B eA w
  have hd : wv m B eA (w + 1) / 2 ^ (64 * w) = (word m B (eA + 8 * w)).toNat := by
    rw [wv, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hl, Nat.zero_add]
  apply decide_eq_decide.mpr
  rw [hP, ← hd, Nat.le_div_iff_mul_le (Nat.two_pow_pos _), Nat.mul_comm (2 ^ 63)]

/-- A word of `addBack`'s sum. -/
theorem addB_arith {A M W P r a mj co ci : Nat} (g : Bool) (h : A + P * ci = M + (if g then W else 0))
    (hs : r + 2 ^ 64 * co = a + (if g then mj else 0) + ci) :
    A + P * r + P * 2 ^ 64 * co = M + P * a + (if g then W + P * mj else 0) := by
  have e : A + P * r + P * 2 ^ 64 * co = A + P * (r + 2 ^ 64 * co) := by
    rw [Nat.mul_add, Nat.mul_assoc]; omega
  rw [e, hs]
  cases g
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h ⊢
    rw [Nat.mul_add]; omega
  · simp only [↓reduceIte] at h ⊢
    rw [Nat.mul_add, Nat.mul_add]; omega

/-- The top word of `addBack`'s sum. -/
theorem addB_tail {Wt Ws P r co top c G : Nat} (h : Wt + P * c = Ws + G) (hs : r + 2 ^ 64 * co = top + 0 + c) :
    Wt + P * r + P * 2 ^ 64 * co = Ws + P * top + G := by
  rw [Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, hs, Nat.add_zero, Nat.mul_add]
  omega

/-- After `j` words of `addBack`'s loop, from the memory `m₀` and the state
`s₀` after its head, adding `m` if `g`. -/
structure AddBInv (m₀ : Mem) (s₀ : State) (B : Addr) (Z eA eM : Nat) (g : Bool) (j : Nat) (t : State) :
    Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eA + 8 * j)
  x17 : t.gpr .x17 = off B (eM + 8 * j)
  out : Outside B eA (8 * j) m₀ t.mem
  val : wv t.mem B eA j + 2 ^ (64 * j) * t.c.toNat = wv m₀ B eA j + if g then wv m₀ B eM j else 0

theorem addBStep_ok {m₀ : Mem} {s₀ : State} {B : Addr} {Z w eA eM : Nat} {g : Bool}
    (h15 : s₀.gpr .x15 = mask g) (hA : eA + 8 * (w + 1) ≤ Z) (hM : eM + 8 * w ≤ Z)
    (sM : eA + 8 * (w + 1) ≤ eM ∨ eM + 8 * w ≤ eA) {j : Nat} (hj : j < w)
    {t : State} (hI : AddBInv m₀ s₀ B Z eA eM g j t) :
    WP isa (.block ([ld .x4 .x17, .logic .and .x .x4 .x4 .x15, ld .x3 .x16, .adcs .x .x3 .x3 .x4, st .x3 .x16,
        next .x16, next .x17] ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      AddBInv m₀ s₀ B Z eA eM g (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t15 : t.gpr .x15 = mask g := (hI.keep.gpr .x15 (by decide)).trans h15
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eA + 8 * j)) (word t.mem B (eA + 8 * j) +
        (word t.mem B (eM + 8 * j) &&& mask g) + BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (eA + 8 * j)).toNat + (word t.mem B (eM + 8 * j) &&& mask g).toNat +
        t.c.toNat) ∧
      t₁.gpr .x16 = off B (eA + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eM + 8 * j + 8))
    (by brun [hI.x16, hI.x17, t15, hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega),
      hI.scr.ld (show eM + 8 * j + 8 ≤ Z by omega), hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hx : word t.mem B (eM + 8 * j) = word m₀ B (eM + 8 * j) :=
    hI.out.word (d := eM + 8 * j) (by omega) (by omega)
  have hy : word t.mem B (eA + 8 * j) = word m₀ B (eA + 8 * j) :=
    hI.out.word (d := eA + 8 * j) (Or.inr (Nat.le_refl _)) (by omega)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    exact fun x hx' => (writeW_outside t.mem B _ (by omega) x (by omega)).trans (hI.out x (by omega))
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hc', hc]
    have hs := adcs_val (word t.mem B (eA + 8 * j)) (word t.mem B (eM + 8 * j) &&& mask g) t.c
    rw [and_mask_toNat, hx, hy] at hs
    rw [and_mask_toNat, hx, hy, pow64_succ, wv, wv]
    exact addB_arith g hI.val hs

/-- `addBack`: `m` (the `w` words at `x9`) added to the `w + 1` words `t` of
the accumulator (at `x8`) if `t ≥ 2^(64 (w + 1)) / 2`, with the carry `c`
out of the top word. -/
theorem r2dAddBack_ok {s : State} {B : Addr} {Z w eA eM : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .x8 = off B eA) (h9 : s.gpr .x9 = off B eM) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : s.gpr .x7 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hA : eA + 8 * (w + 1) ≤ Z) (hM : eM + 8 * w ≤ Z) (sM : eA + 8 * (w + 1) ≤ eM ∨ eM + 8 * w ≤ eA) :
    WP isa addBack s fun t => ∃ c : Bool,
      wv t.mem B eA (w + 1) + 2 ^ (64 * (w + 1)) * c.toNat =
        wv s.mem B eA (w + 1) + (if 2 ^ (64 * (w + 1)) / 2 ≤ wv s.mem B eA (w + 1) then wv s.mem B eM w else 0) ∧
      Outside B eA (8 * (w + 1)) s.mem t.mem ∧ Keep [.x3, .x4, .x13, .x14, .x15, .x16, .x17] s t := by
  have hn := hs.nowrap
  generalize hg : decide (2 ^ 63 ≤ (word s.mem B (eA + 8 * w)).toNat) = g
  unfold addBack
  refine WP.seq (WP.mono (WP.keep [.x3, .x13, .x14, .x15, .x16, .x17] (Q := fun t =>
    t.gpr .x15 = mask g ∧ t.gpr .x16 = off B eA ∧ t.gpr .x17 = off B eM ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧
    t.c = false ∧ t.mem = s.mem)
    (by brun [h8, h9, h12, h7, r2d_ofNat_shl3 (show w < 2 ^ 61 by omega), hs.ld (show eA + 8 * w + 8 ≤ Z by omega),
        hg]; exact (sign_mask _).trans (congrArg mask hg)) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h15, h16, h17, h14, hc₁, hm₁⟩, k₁⟩ => ?_)
  have h0 : AddBInv s.mem s₁ B Z eA eM g 0 s₁ :=
    ⟨hs.congr k₁.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, by rw [hm₁]; exact Outside.refl _ _ _ _,
      by rw [hc₁]; cases g <;> rfl⟩
  refine WP.seq (WP.mono (wp_countdown (N := w) (by omega) (by omega) (AddBInv s.mem s₁ B Z eA eM g)
    (fun j hj t hI _ => addBStep_ok h15 hA hM sM hj hI) h0 h14) fun t hI => ?_)
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans ((k₁.gpr .x7 (by decide)).trans h7)
  have hy : word t.mem B (eA + 8 * w) = word s.mem B (eA + 8 * w) :=
    hI.out.word (d := eA + 8 * w) (Or.inr (Nat.le_refl _)) (by omega)
  refine WP.mono (WP.keep [.x3] (Q := fun t' =>
      t'.mem = t.mem.writeW (off B (eA + 8 * w)) (word t.mem B (eA + 8 * w) + 0 + BitVec.ofNat 64 t.c.toNat))
    (by brun [hI.x16, t7, hI.scr.ld (show eA + 8 * w + 8 ≤ Z by omega),
      hI.scr.st (show eA + 8 * w + 8 ≤ Z by omega)]) (by decide) (by decide) (by decide +kernel))
    fun t' ⟨hm', k'⟩ => ?_
  have hs' := adcs_val (word t.mem B (eA + 8 * w)) 0 t.c
  refine ⟨decide (2 ^ 64 ≤ (word t.mem B (eA + 8 * w)).toNat + (0 : BitVec 64).toNat + t.c.toNat), ?_, ?_,
    ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  · have hT : (2 ^ (64 * (w + 1)) / 2 ≤ wv s.mem B eA (w + 1)) = (g = true) := by
      rw [← hg, sign_top, decide_eq_true_eq]
    simp only [hT]
    rw [hm', wv_writeW_top _ _ _ _ _ (by omega), wv, ← hy, pow64_succ]
    exact addB_tail hI.val hs'
  · rw [hm']
    exact fun x hx' => (writeW_outside t.mem B _ (by omega) x (by omega)).trans (hI.out x (by omega))

end VG.Proof.Bignum.AArch64
