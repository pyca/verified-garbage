module

public import VerifiedGarbage.Proof.Rsa.AArch64.WDiv
public import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.MlKem.AArch64.Wp

/-!
# `vg_rsa_crt_values` on AArch64: the inverse's tail by words

When `wordGuard` passes, `inverseAtS` leaves `x₂ < p` with `x₂ 2^K` the
inverse, `K = 15 n + 10 = 64 Q + T` (`tail_split`), and `qTail` computes
`x₂ 2^K mod p`: `T ≤ 64` doublings of `x₂` in place over `n + 1` words
(`tailDbl_ok`: `x₂ 2^T < 2^(64 (n + 1))`, as `x₂ < 2^(64 n)`), the result
copied `Q` words up into the zeroed `[aC]` (`place`), and `wdiv` of its
`n + Q + 1` words by `p` into `[aX₂]` (`qTail_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.Keys.CrtValues
open VG.Impl.Rsa.AArch64.InvBatch (dblBody)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The whole words `Q` and the doublings `T` of `K = 15 n + 10`. -/
def tailQ (n : Nat) : Nat := (15 * n + 9) / 64
def tailT (n : Nat) : Nat := (15 * n + 9) % 64 + 1

theorem tail_split (n : Nat) : 15 * n + 10 = 64 * tailQ n + tailT n := by
  unfold tailQ tailT; omega

/-- `tailK`: `n`, `Q` and `T` from `w = 2 n`. -/
theorem tailK_ok {t : State} {w : Nat} (h12 : t.gpr .x12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 24) :
    WP isa (.block tailK) t fun t' =>
      (t'.gpr .x5 = BitVec.ofNat 64 (w / 2) ∧ t'.gpr .x13 = BitVec.ofNat 64 (tailQ (w / 2)) ∧
        t'.gpr .x15 = BitVec.ofNat 64 (tailT (w / 2)) ∧ t'.mem = t.mem) ∧
      Keep [.x3, .x5, .x6, .x13, .x15] t t' := by
  have e5 : BitVec.ofNat 64 w >>> 1 = BitVec.ofNat 64 (w / 2) := by
    rw [shr_ofNat (show w < 2 ^ 64 by omega_arith)]
  have e6 : (BitVec.ofNat 64 (w / 2) <<< 4 - BitVec.ofNat 64 (w / 2)) + BitVec.ofNat 64 9 =
      BitVec.ofNat 64 (15 * (w / 2) + 9) := by
    rw [shl_ofNat (show w / 2 * 2 ^ 4 < 2 ^ 64 by omega_arith)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith
  refine WP.keep [.x3, .x5, .x6, .x13, .x15] ?_ (by decide) (by decide) (by decide +kernel)
  unfold tailK
  brun [h12, e5, e6, shr_ofNat (show 15 * (w / 2) + 9 < 2 ^ 64 by omega_arith)]
  refine ⟨rfl, ?_⟩
  unfold tailT
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.reduceMod,
    Nat.reducePow]
  rw [show ∀ x : Nat, x &&& 63 = x % 64 from fun x => Nat.and_two_pow_sub_one_eq_mod x 6]
  rw [Nat.mod_eq_of_lt (show 15 * (w / 2) + 9 < 18446744073709551616 by omega)]

/-- A word of a doubling in place (`dblStep_ok` with the source the
destination): the word it reads is not yet written. -/
theorem dblIPStep_ok {s₀ : State} {B : Addr} {Z w eA : Nat} (hA : eA + 8 * w ≤ Z) {j : Nat} (hj : j < w)
    {t : State} (hI : DblInv s₀ B Z eA eA j t) :
    WP isa (.block (dblBody ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      DblInv s₀ B Z eA eA (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eA + 8 * j)) (word t.mem B (eA + 8 * j) + word t.mem B (eA + 8 * j) +
        BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (eA + 8 * j)).toNat + (word t.mem B (eA + 8 * j)).toNat +
        t.c.toNat) ∧
      t₁.gpr .x16 = off B (eA + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eA + 8 * j + 8))
    (by brun [dblBody, hI.x16, hI.x17, hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hy : word t.mem B (eA + 8 * j) = word s₀.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hc', hc]
    have hs := adcs_toNat (word t.mem B (eA + 8 * j)) (word t.mem B (eA + 8 * j)) t.c
    rw [hy] at hs
    have hval := hI.val
    simp only [wv]
    rw [pow64_succ, hy]
    grind

/-- After `j` of `tailDbl`'s doublings from `s₀`: `[aX₂]`'s low `n + 1`
words are `X 2^j`. -/
structure TDInv (s₀ : State) (B : Addr) (Z w n X : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  x0 : t.gpr .x0 = B
  x11 : t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))
  x5 : t.gpr .x5 = BitVec.ofNat 64 n
  out : Outside B (slot w aX₂) (8 * (n + 1)) s₀.mem t.mem
  keep : Keep [.x3, .x7, .x14, .x16, .x17, .x15] s₀ t
  val : X * 2 ^ j < 2 ^ (64 * (n + 1)) → wv t.mem B (slot w aX₂) (n + 1) = X * 2 ^ j

/-- A pass of `tailDbl`: `[aX₂]`'s low `n + 1` words doubled, when that fits. -/
theorem tailPass_ok {t : State} {B : Addr} {Z w n : Nat} (hs : Scr t B Z) (h0 : t.gpr .x0 = B)
    (h11 : t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h5 : t.gpr .x5 = BitVec.ofNat 64 n) (hn : n + 1 ≤ w + 2)
    (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) :
    WP isa (.seq (.block dblSetup) (.seq (countLoop .x14 dblBody) (.block [.subImm .x .x15 .x15 1]))) t fun t' =>
      Scr t' B Z ∧ Outside B (slot w aX₂) (8 * (n + 1)) t.mem t'.mem ∧ Keep [.x3, .x7, .x14, .x16, .x17, .x15] t t' ∧
      (2 * wv t.mem B (slot w aX₂) (n + 1) < 2 ^ (64 * (n + 1)) →
        wv t'.mem B (slot w aX₂) (n + 1) = 2 * wv t.mem B (slot w aX₂) (n + 1)) ∧
      t'.gpr .x15 = t.gpr .x15 - BitVec.ofNat 64 1 := by
  have hn' := hs.nowrap
  have sX := Nat.le_trans (slot_lt (w := w) (show aX₂ < 16 by decide)) hZ
  unfold dblSetup
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base_ok aX₂ .x16 h0 h11) fun t₁ ⟨⟨h16, m₁, _⟩, k₁⟩ =>
    WP.mono (WP.keep [.x17, .x14, .x7, .x3] (Q := fun t₂ => t₂.gpr .x17 = off B (slot w aX₂) ∧
        t₂.gpr .x14 = BitVec.ofNat 64 (n + 1) ∧ t₂.gpr .x7 = 0 ∧ t₂.c = false ∧ t₂.mem = t₁.mem)
      (by brun [h16, (k₁.gpr .x5 (by decide)).trans h5, BitVec.ofNat_add_ofNat]) (by decide) (by decide)
      (by decide +kernel)) fun t₂ ⟨⟨h17, h14, _, hc, m₂⟩, k₂⟩ => ?_))
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have hm₂ : t₂.mem = t.mem := by rw [m₂, m₁]
  have i0 : DblInv t₂ B Z (slot w aX₂) (slot w aX₂) 0 t₂ :=
    ⟨hs₂, Keep.refl _ _, by rw [(k₂.gpr .x16 (by decide)).trans h16]; rfl, by rw [h17]; rfl, Outside.refl _ _ _ _,
      by rw [hc]; rfl⟩
  refine WP.seq (WP.mono (wp_countdown (N := n + 1) (by omega_arith) (by omega_arith)
    (DblInv t₂ B Z (slot w aX₂) (slot w aX₂))
    (fun j hj t hI _ => dblIPStep_ok (w := n + 1) (by omega_arith) hj hI) i0 h14) fun t₃ hD => ?_)
  refine WP.mono (dec_ok t₃ .x15) fun t' ⟨⟨h15, hm', _⟩, k'⟩ => ?_
  have k3 := hD.keep
  refine ⟨hD.scr.congr k'.wr, ?_, ((k12.trans k3).trans k').mono (by decide), fun hlt => ?_,
    by rw [h15, k3.gpr .x15 (by decide), k12.gpr .x15 (by decide)]⟩
  · rw [hm', ← hm₂]; exact hD.out
  · have hv := hD.val
    rw [hm₂] at hv
    rw [hm']
    have := wv_lt t₃.mem B (slot w aX₂) (n + 1)
    rcases Nat.eq_zero_or_pos t₃.c.toNat with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero] at hv; exact hv
    · have := Nat.mul_le_mul_left (2 ^ (64 * (n + 1))) h; omega_arith

/-- `tailDbl`: `T` doublings in place of `[aX₂]`'s low `n + 1` words. -/
theorem tailDbl_ok {s : State} {B : Addr} {Z w n T : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h5 : s.gpr .x5 = BitVec.ofNat 64 n) (hn : n + 1 ≤ w + 2)
    (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) (hT : 0 < T) (hT' : T < 2 ^ 64)
    (h15 : s.gpr .x15 = BitVec.ofNat 64 T) :
    WP isa tailDbl s (TDInv s B Z w n (wv s.mem B (slot w aX₂) (n + 1)) T) := by
  refine wp_countdown (N := T) hT' hT _ (fun j _ t hI _ => ?_)
    ⟨hs, h0, h11, h5, Outside.refl _ _ _ _, Keep.refl _ _, fun _ => by rw [Nat.pow_zero, Nat.mul_one]⟩ h15
  refine WP.mono (tailPass_ok hI.scr hI.x0 hI.x11 hI.x5 hn hw hZ) fun t' ⟨sc, o, k, v, c⟩ => ⟨⟨sc,
    (k.gpr .x0 (by decide)).trans hI.x0, (k.gpr .x11 (by decide)).trans hI.x11, (k.gpr .x5 (by decide)).trans hI.x5,
    hI.out.trans o, (hI.keep.trans k).mono (by decide), fun hlt => ?_⟩, c⟩
  have hlt' : wv s.mem B (slot w aX₂) (n + 1) * 2 ^ j < 2 ^ (64 * (n + 1)) :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.le_succ j))) hlt
  have hv := hI.val hlt'
  rw [v (by rw [hv, ← Nat.mul_assoc, Nat.mul_comm 2, Nat.mul_assoc, ← Nat.pow_succ']; exact hlt), hv, Nat.pow_succ]
  ac_rfl

/-- `tailLen`: `L = n + Q + 1 = ⌊(79 n + 9) / 64⌋ + 1` from `w = 2 n`. -/
theorem tailLen_ok (w : Nat) (hw2 : w % 2 = 0) (hw : w < 2 ^ 24) :
    LenOk tailLen w (w / 2 + tailQ (w / 2) + 1) := fun t h12 => by
  have e1 : BitVec.ofNat 64 w <<< 2 = BitVec.ofNat 64 (4 * w) := by
    rw [shl_ofNat (show w * 2 ^ 2 < 2 ^ 64 by omega_arith), Nat.mul_comm]
  have e2 : BitVec.ofNat 64 (4 * w) + BitVec.ofNat 64 w = BitVec.ofNat 64 (5 * w) := by
    rw [BitVec.ofNat_add_ofNat]; congr 1; omega
  have e3 : BitVec.ofNat 64 (5 * w) <<< 4 = BitVec.ofNat 64 (80 * w) := by
    rw [shl_ofNat (show 5 * w * 2 ^ 4 < 2 ^ 64 by omega_arith)]; congr 1; omega
  have e4 : BitVec.ofNat 64 (80 * w) - BitVec.ofNat 64 w = BitVec.ofNat 64 (79 * w) := by
    rw [bv_sub_ofNat (by omega) (by omega_arith)]; congr 1; omega
  have e5 : BitVec.ofNat 64 (79 * w) >>> 1 = BitVec.ofNat 64 (79 * w / 2) := by
    rw [shr_ofNat (show 79 * w < 2 ^ 64 by omega_arith)]
  have e6 : BitVec.ofNat 64 (79 * w / 2) + BitVec.ofNat 64 9 = BitVec.ofNat 64 (79 * w / 2 + 9) := by
    rw [BitVec.ofNat_add_ofNat]
  have e7 : BitVec.ofNat 64 (79 * w / 2 + 9) >>> 6 = BitVec.ofNat 64 ((79 * w / 2 + 9) / 64) := by
    rw [shr_ofNat (show 79 * w / 2 + 9 < 2 ^ 64 by omega_arith)]
  have e8 : BitVec.ofNat 64 ((79 * w / 2 + 9) / 64) + BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (w / 2 + tailQ (w / 2) + 1) := by
    rw [BitVec.ofNat_add_ofNat]; congr 1; unfold tailQ; omega
  refine WP.keep [.x13] (Q := fun t' => t'.gpr .x13 = BitVec.ofNat 64 (w / 2 + tailQ (w / 2) + 1) ∧
    t'.mem = t.mem) ?_ (by decide) (by decide) (by decide +kernel)
  unfold tailLen
  brun [h12, e1, e2, e3, e4, e5, e6, e7, e8]

/-- `qTail`'s dividend `[aC]`, two arrays above `[aX₂]`. -/
theorem tailXb_ok (B : Addr) (w : Nat) (hw : w % 2 = 0) (hw' : w < 2 ^ 24) :
    XbOk [.lsl .x .x16 .x12 5, .addImm .x .x16 .x16 24, .add .x .x16 .x11 .x16] B (slot w aX₂) (slot w aC)
      (w / 2) := fun t h11 h12 => by
  have e : off B (slot w aX₂) + BitVec.ofNat 64 (32 * (w / 2) + 24) = off B (slot w aC - 8) := by
    rw [off_add]; congr 1; simp only [slot, aX₂, aC]; omega_arith
  refine WP.keep [.x16] (Q := fun t' => t'.gpr .x16 = off B (slot w aC - 8) ∧ t'.mem = t.mem)
    ?_ (by decide) (by decide) (by decide +kernel)
  brun [h11, h12, shl5_ofNat (show w / 2 < 2 ^ 58 by omega_arith)]
  rw [← e, BitVec.ofNat_add, BitVec.add_comm]

/-- `place`: `x16 := [aX₂]`'s base, `x17 :=` `[aC]`'s word `Q`, `x12 := n + 1`. -/
theorem placeBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block place) s fun t =>
      (t.gpr .x16 = off B (slot w aX₂) ∧ t.gpr .x17 = off B (slot w aC + 8 * tailQ (w / 2)) ∧
        t.gpr .x12 = BitVec.ofNat 64 (w / 2 + 1) ∧ t.mem = s.mem) ∧
      Keep [.x3, .x5, .x6, .x11, .x12, .x13, .x15, .x16, .x17] s t := by
  have hw := h.w2
  simp only [place, placeRest, List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (tailK_ok h12 hw) fun s₂ ⟨⟨h5, h13, _, m₂⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.block_append_iff.mpr (WP.mono (base_ok aX₂ .x16 ((k12.gpr .x0 (by decide)).trans h.x0)
    ((k₂.gpr .x11 (by decide)).trans h11)) fun s₃ ⟨⟨h16, m₃, _⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  refine WP.block_append_iff.mpr (WP.mono (base_ok aC .x17 ((k13.gpr .x0 (by decide)).trans h.x0)
    ((k₃.gpr .x11 (by decide)).trans ((k₂.gpr .x11 (by decide)).trans h11)) (by decide)) fun s₄ ⟨⟨h17, m₄, _⟩, k₄⟩ => ?_)
  have k14 := k13.trans k₄
  have e3 : BitVec.ofNat 64 (tailQ (w / 2)) <<< 3 = BitVec.ofNat 64 (8 * tailQ (w / 2)) := by
    rw [shl_ofNat (show tailQ (w / 2) * 2 ^ 3 < 2 ^ 64 by unfold tailQ; omega_arith), Nat.mul_comm]
  refine WP.mono (WP.keep [.x3, .x17, .x12] (Q := fun t => t.gpr .x17 = off B (slot w aC + 8 * tailQ (w / 2)) ∧
      t.gpr .x12 = BitVec.ofNat 64 (w / 2 + 1) ∧ t.mem = s₄.mem)
    (by brun [h17, (k₄.gpr .x13 (by decide)).trans ((k₃.gpr .x13 (by decide)).trans h13),
      (k₄.gpr .x5 (by decide)).trans ((k₃.gpr .x5 (by decide)).trans h5), e3, off_add, BitVec.ofNat_add_ofNat])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨t17, t12, mt⟩, kt⟩ =>
      ⟨⟨(kt.gpr .x16 (by decide)).trans ((k₄.gpr .x16 (by decide)).trans h16), t17, t12,
        by rw [mt, m₄, m₃, m₂, m₁]⟩, (k14.trans kt).mono (by decide)⟩

/-- `qTail`: `[aX₂] := [aX₂] 2^(15 n + 10) mod p` (`n = w / 2`) for `[aX₂] < p`
and `p` of `n` words with its top bit set; it writes only `[aX₂]`, `[aC]`
and `[aT]`. -/
theorem qTail_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (hw2 : w % 2 = 0) (hw8 : 8 ≤ w) :
    WP isa (seqs qTail) s fun t => t.gpr .x0 = B ∧ Frm B [ar w aX₂, ar w aC, ar w aT] s.mem t.mem ∧
      Keep wdRegs s t ∧
      (wv s.mem B (slot w aX₂) w < wv s.mem B (slot w aP) w →
        2 ^ (64 * (w / 2) - 1) ≤ wv s.mem B (slot w aP) w → wv s.mem B (slot w aP) w < 2 ^ (64 * (w / 2)) →
        wv t.mem B (slot w aX₂) w =
          wv s.mem B (slot w aX₂) w * 2 ^ (15 * (w / 2) + 10) % wv s.mem B (slot w aP) w) := by
  have hs := h.scr
  have hn' := hs.nowrap
  have hw := h.w2
  have hZ := h.hZ
  have sl : ∀ j < 16, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_lt (w := w) hj) hZ
  have sX := sl aX₂ (by decide)
  have sC := sl aC (by decide)
  have hQ : tailQ (w / 2) + (w / 2 + 1) ≤ w + 2 := by unfold tailQ; omega
  have hT1 : 0 < tailT (w / 2) := by unfold tailT; omega
  have hT64 : tailT (w / 2) ≤ 64 := by unfold tailT; omega
  have eXC : slot w aC = slot w aX₂ + 16 * (w + 2) := by simp only [slot, aC, aX₂]; omega
  simp only [qTail, seqs]
  -- `n`, `Q` and `T`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ =>
    WP.mono (tailK_ok h12 hw) fun s₂ ⟨⟨h5, _, h15, m₂⟩, k₂⟩ => ?_))
  have k12 := k₁.trans k₂
  have hm₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  -- `T` doublings.
  refine WP.seq (WP.mono (tailDbl_ok (hs.congr k12.wr) ((k12.gpr .x0 (by decide)).trans h.x0)
    ((k₂.gpr .x11 (by decide)).trans h11) h5 (by omega) hw hZ hT1 (by omega) h15) fun s₃ hD => ?_)
  have hDo : Outside B (slot w aX₂) (8 * (w / 2 + 1)) s.mem s₃.mem := by rw [← hm₂]; exact hD.out
  have W₃ : Ws s₃ B Z w := h.congr (rs := [(slot w aX₂, 8 * (w / 2 + 1))]) (Frm.of_outside hDo (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) (k12.trans hD.keep) (by decide)
  -- `[aC] := 0`.
  refine WP.seq (WP.mono (zeroA_ok W₃ (j := aC) (by decide)) fun s₄ ⟨z₄, o₄, _, _, _, k₄⟩ => ?_)
  have W₄ : Ws s₄ B Z w := W₃.congr (rs := [ar w aC]) (Frm.of_outside o₄ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) k₄ (by decide)
  -- `[aX₂]`'s `n + 1` words to `[aC]`'s from `Q`.
  refine WP.seq (WP.mono (placeBlk_ok W₄) fun s₅ ⟨⟨h16, h17, h12', m₅⟩, k₅⟩ => ?_)
  have hs₅ := W₄.scr.congr k₅.wr
  refine WP.seq (WP.mono (copyWords_ok (S := B) (D := B) (w := w / 2 + 1) h16 h17 h12' (by omega) (by omega)
    (by omega_arith) (fun j _ => hs₅.ld (by omega_arith)) (fun j _ => hs₅.st (by omega_arith))
    (fun j hj b hb => by rw [ofs_off B (by omega_arith)]; exact Or.inl (by omega_arith))) fun s₆ ⟨c₆, _, o₆, _, _, k₆⟩ => ?_)
  have f₆ : Frm B [ar w aC] s₄.mem s₆.mem := by
    rw [← m₅]
    exact Frm.widen (Frm.of_outside o₆ (List.mem_singleton_self _)) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, by dsimp only [ar]; omega,
        by dsimp only [ar]; omega⟩
  have W₆ : Ws s₆ B Z w := W₄.congr (rs := [ar w aC]) f₆ (fun r hr => by rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _)
    (k₅.trans k₆) (by decide)
  -- The remainder.
  refine WP.mono (wdiv_ok W₆ (iX := aC) (iM := aP) (iR := aX₂) (iT := aT) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (cvWm_ok w hw) (tailLen_ok w hw2 hw)
    (tailXb_ok B w hw2 hw) (by omega) (by omega) (by omega) (by omega)) fun t ⟨t0, ft, kt, hv⟩ => ?_
  -- Each piece writes only its own arrays.
  have fX : Frm B [ar w aX₂, ar w aC, ar w aT] s.mem s₃.mem :=
    Frm.widen (Frm.of_outside hDo (List.mem_singleton_self _)) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨ar w aX₂, by simp, by dsimp only [ar]; omega, by dsimp only [ar]; omega⟩
  have fC : ∀ {m m' : Mem}, Frm B [ar w aC] m m' → Frm B [ar w aX₂, ar w aC, ar w aT] m m' := fun f =>
    Frm.mono f (by simp)
  have fR : Frm B [ar w aX₂, ar w aC, ar w aT] s₆.mem t.mem := Frm.mono ft (by simp)
  refine ⟨t0, ((fX.trans (fC (Frm.of_outside o₄ (by simp [ar])))).trans (fC f₆)).trans fR,
    ((((k12.trans hD.keep).trans k₄).trans (k₅.trans k₆)).trans kt).mono (by decide), fun hXP hlo hhi => ?_⟩
  -- The values.
  have hP0 : 0 < wv s.mem B (slot w aP) w := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hlo
  have pX : ∀ {m m' : Mem}, Frm B [ar w aX₂, ar w aC, ar w aT] m m' →
      wv m' B (slot w aP) w = wv m B (slot w aP) w := fun f => f.wv_eq (fun r hr => by
    simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only
    · have := slot_sep (w := w) (show aP ≠ aX₂ by decide); omega
    · have := slot_sep (w := w) (show aP ≠ aC by decide); omega
    · have := slot_sep (w := w) (show aP ≠ aT by decide); omega) (by have := sl aP (by decide); omega)
  have P₆ : wv s₆.mem B (slot w aP) w = wv s.mem B (slot w aP) w :=
    pX (((fX.trans (fC (Frm.of_outside o₄ (by simp [ar])))).trans (fC f₆)))
  have hXn : (wv s.mem B (slot w aX₂) w) < 2 ^ (64 * (w / 2)) := Nat.lt_trans hXP hhi
  have X1 : wv s.mem B (slot w aX₂) (w / 2 + 1) = (wv s.mem B (slot w aX₂) w) :=
    wv_low_of_lt (by omega) (Nat.lt_of_lt_of_le hXn (Nat.pow_le_pow_right (by decide) (by omega)))
  have hfit : (wv s.mem B (slot w aX₂) w) * 2 ^ tailT (w / 2) < 2 ^ (64 * (w / 2 + 1)) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le hXn (Nat.pow_le_pow_right (by decide) hT64) (Nat.two_pow_pos _)
  have D₃ : wv s₃.mem B (slot w aX₂) (w / 2 + 1) = (wv s.mem B (slot w aX₂) w) * 2 ^ tailT (w / 2) := by
    have hv := hD.val
    rw [hm₂, X1] at hv
    exact hv hfit
  -- `[aC]` holds `(wv s.mem B (slot w aX₂) w) 2^K` in its `L` words.
  have C₆ : wv s₆.mem B (slot w aC) (w / 2 + tailQ (w / 2) + 1) = (wv s.mem B (slot w aX₂) w) * 2 ^ (15 * (w / 2) + 10) := by
    rw [show w / 2 + tailQ (w / 2) + 1 = tailQ (w / 2) + (w / 2 + 1) by omega, wv_add, c₆]
    have lo : wv s₆.mem B (slot w aC) (tailQ (w / 2)) = 0 := by
      rw [o₆.wv (Or.inl (by omega)) (by omega), m₅]
      have hz : ∀ q < w + 2, word s₄.mem B (slot w aC + 8 * q) = 0 := (wv_eq_zero_iff _ _ _ _).mp z₄
      exact wv_zero fun q hq => hz q (by omega)
    have hi : wv s₅.mem B (slot w aX₂) (w / 2 + 1) = (wv s.mem B (slot w aX₂) w) * 2 ^ tailT (w / 2) := by
      rw [m₅, o₄.wv (Or.inl (by omega)) (by omega), D₃]
    rw [lo, hi, Nat.zero_add, tail_split, Nat.pow_add, Nat.pow_mul]
    ac_rfl
  -- `p`'s top bit.
  have Pn : wv s₆.mem B (slot w aP) (w / 2) = (wv s.mem B (slot w aP) w) := by
    rw [wv_low_of_lt (v := w / 2) (w := w) (by omega) (by rw [P₆]; exact hhi), P₆]
  have htop : 2 ^ 63 ≤ (word s₆.mem B (slot w aP + 8 * (w / 2 - 1))).toNat := by
    rw [word_of_wv _ _ _ (w / 2) (by omega), Pn]
    exact top_word_of (by omega) hlo hhi
  have hv := hv htop
  rw [C₆, Pn] at hv
  have hlt : wv t.mem B (slot w aX₂) (w + 2) < 2 ^ (64 * w) := by
    rw [hv]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hP0) (Nat.le_of_lt (Nat.lt_of_lt_of_le hhi
      (Nat.pow_le_pow_right (by decide) (by omega))))
  rw [wv_low_of_lt (by omega) hlt, hv]

end VG.Proof.Rsa.AArch64
