module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
import VerifiedGarbage.Proof.Rsa.AArch64.RdTwos
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `vg_rsa_recover_primes_det` on AArch64: products

`product_ok`: `64 v` steps of `RecoverDet.prodStep`, the multiplier `y`
narrow and the multiplicand `x` and the sum `a` wide, through the wide `t`.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa.RecoverDet

/-- The multiplier's low bit, as a mask in `x15`. -/
theorem prodBit_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {y : Nat} (hy : y < 16) :
    WP isa (.block (ws ++ base y .x16 ++ [ld .x3 .x16, movi .x7 0] ++ oddMask)) s fun t =>
      (t.gpr .x15 = mask (decide (wv s.mem B (slot w y) w % 2 = 1)) ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem) ∧
      Keep [.x3, .x4, .x7, .x11, .x12, .x15, .x16] s t := by
  have hw1 : 1 ≤ w := by have := h.w1; omega
  have hn := h.scr.nowrap
  have sy := h.sl hy
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨⟨_, h11, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok y .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun t₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).wr
  refine WP.mono (WP.keep [.x3, .x4, .x7, .x15] (Q := fun t => (t.gpr .x15 = mask (decide ((word s.mem B
      (slot w y)).toNat % 2 = 1)) ∧ t.gpr .x7 = 0) ∧ t.mem = t₂.mem)
    (by brun [oddMask, h16, hs₂.ld (d := slot w y) (by omega), m₂, m₁, mask_low']) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨⟨h15, h7⟩, mt⟩, k₃⟩ => ⟨⟨by rw [h15, par_word hw1], h7, by rw [mt, m₂, m₁]⟩,
      ((k₁.trans k₂).trans k₃).mono (by decide)⟩

theorem prodStep_val (b Y X A : Nat) :
    prodStep b (Y, X, A) = (Y / 2, (2 * X + false.toNat) % 2 ^ b,
      ((if decide (Y % 2 = 1) then X else 0) + A) % 2 ^ b) := by
  unfold prodStep
  rcases Nat.mod_two_eq_zero_or_one Y with e | e <;> simp [e, Nat.add_comm]

/-- The arrays of a product: `y` narrow, `x`, `a` and `t` wide, apart. -/
structure PIdx (y x a t : Nat) : Prop where
  hy : y < 16
  hx : x < 8
  ha : a < 8
  ht : t < 16
  xa : x ≠ a
  xt : x ≠ t
  at' : a ≠ t
  yx1 : y ≠ 2 * x
  yx2 : y ≠ 2 * x + 1
  ya1 : y ≠ 2 * a
  ya2 : y ≠ 2 * a + 1
  yt1 : y ≠ 2 * t
  yt2 : y ≠ 2 * t + 1

/-- The ranges a product writes. -/
abbrev prodRanges (v y x a t : Nat) : List (Nat × Nat) :=
  hdrW ++ [(slot v y, 8 * v), (slot (2 * v + 2) t, 8 * (2 * v + 2)), (slot (2 * v + 2) a, 8 * (2 * v + 2)),
    (slot (2 * v + 2) x, 8 * (2 * v + 2))]

/-- After `j` steps of a product from `s₀`. -/
structure PI (I : RpIn) (m₀ : Mem) (c : Bool) (y x a t : Nat) (s₀ : State) (st : Nat × Nat × Nat) (j : Nat)
    (u : State) : Prop where
  g : G I m₀ (vk I.k) c u
  val : (wv u.mem I.B (slot (vk I.k) y) (vk I.k), wv u.mem I.B (slot (Wk I.k) x) (Wk I.k),
    wv u.mem I.B (slot (Wk I.k) a) (Wk I.k)) = (prodStep (64 * Wk I.k))^[j] st
  zY : word u.mem I.B (slot (vk I.k) y + 8 * vk I.k) = 0
  frm : Frm I.B (prodRanges (vk I.k) y x a t) s₀.mem u.mem

theorem prodStepCode_ok {I : RpIn} {m₀ : Mem} {c : Bool} {y x a t : Nat} {s₀ : State} {st : Nat × Nat × Nat}
    {j : Nat} {u : State} (L : RpLens I) (P : PIdx y x a t) (hI : PI I m₀ c y x a t s₀ st j u) :
    WP isa (prodBody y x a t) u fun u' => PI I m₀ c y x a t s₀ st (j + 1) u' ∧
      u'.gpr .x6 = u.gpr .x6 - BitVec.ofNat 64 1 := by
  have g := hI.g
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega
  have hy := P.hy
  have hx16 : x < 16 := by have := P.hx; omega
  have ha16 : a < 16 := by have := P.ha; omega
  have ht := P.ht
  have by' : slot (vk I.k) y + 8 * (vk I.k + 2) ≤ 2 ^ 64 := g.bndv L (by omega) (Nat.le_refl _)
  have bx : slot (Wk I.k) x + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := g.bndW L hx16 (Nat.le_refl _)
  have ba : slot (Wk I.k) a + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := g.bndW L ha16 (Nat.le_refl _)
  have bt : slot (Wk I.k) t + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := g.bndW L ht (Nat.le_refl _)
  have bx' : slot (2 * vk I.k + 2) x + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := bx
  have ba' : slot (2 * vk I.k + 2) a + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := ba
  have bt' : slot (2 * vk I.k + 2) t + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := bt
  generalize hY : wv u.mem I.B (slot (vk I.k) y) (vk I.k) = Y
  generalize hX : wv u.mem I.B (slot (Wk I.k) x) (Wk I.k) = X
  generalize hA : wv u.mem I.B (slot (Wk I.k) a) (Wk I.k) = A
  have hval : (Y, X, A) = (prodStep (64 * Wk I.k))^[j] st := by rw [← hY, ← hX, ← hA]; exact hI.val
  unfold prodBody
  simp only [seqs]
  -- The bit, and `y` halved.
  refine WP.seq (WP.mono (prodBit_ok g.ws hy) fun u₁ ⟨⟨h15, h7, m₁⟩, k₁⟩ => ?_)
  rw [hY] at h15
  have g₁ := g.same m₁ k₁ (by decide)
  refine WP.seq (WP.mono (halfA_ok g₁.ws (o := y) (a := y) hy hy (by rw [m₁]; exact hI.zY))
    fun u₂ ⟨v₂, o₂, k₂⟩ => ?_)
  have g₂ := g₁.out hy (by omega) o₂ k₂ (by decide)
  rw [m₁, hY] at v₂
  -- `t := (x & mask) + a`, `a := t`, `x := 2 x`.
  refine WP.seq (WP.mono (g₂.setWid_ok L) fun u₃ ⟨g₃, f₃, k₃⟩ => ?_)
  have X₃ : wv u₃.mem I.B (slot (Wk I.k) x) (Wk I.k) = X := by
    rw [Frm.hdrW_wv f₃ (slot_ge _ _) (by omega), o₂.wv (wn_sep P.yx1 P.yx2 (by omega) (by omega)) (by omega), m₁, hX]
  have A₃ : wv u₃.mem I.B (slot (Wk I.k) a) (Wk I.k) = A := by
    rw [Frm.hdrW_wv f₃ (slot_ge _ _) (by omega), o₂.wv (wn_sep P.ya1 P.ya2 (by omega) (by omega)) (by omega), m₁, hA]
  have h15₃ : u₃.gpr .x15 = mask (decide (Y % 2 = 1)) := by
    rw [k₃.gpr .x15 (by decide), k₂.gpr .x15 (by decide), h15]
  refine WP.seq (WP.mono (addA_ok g₃.ws (o := t) (a := x) (b := a) ht hx16 ha16 (Ne.symm P.xt) (Ne.symm P.at')
    h15₃) fun u₄ ⟨v₄, _, o₄, k₄⟩ => ?_)
  have g₄ := g₃.out ht (by omega) o₄ k₄ (by decide)
  rw [X₃, A₃] at v₄
  refine WP.seq (WP.mono (copyA_ok g₄.ws (o := a) (a := t) ha16 ht P.at') fun u₅ ⟨v₅, o₅, _, _, k₅⟩ => ?_)
  have g₅ := g₄.out ha16 (by omega) o₅ k₅ (by decide)
  rw [v₄] at v₅
  have X₅ : wv u₅.mem I.B (slot (Wk I.k) x) (Wk I.k) = X := by
    rw [o₅.wv (rd_sep P.xa (by omega) (by omega)) (by omega), o₄.wv (rd_sep P.xt (by omega) (by omega)) (by omega), X₃]
  refine WP.seq (WP.mono (dbl_ok g₅.ws (a := x) hx16 (b := false) (fun t h7 _ => c0_ok t h7))
    fun u₆ ⟨v₆, _, o₆, k₆⟩ => ?_)
  have g₆ := g₅.out hx16 (by omega) o₆ k₆ (by decide)
  rw [X₅] at v₆
  rw [WP.block_append_iff]
  refine WP.mono (g₆.setNar_ok L) fun u₇ ⟨g₇, f₇, k₇⟩ => ?_
  refine WP.mono (dec_ok u₇ .x6) fun u' ⟨⟨h6, m', _⟩, k₈⟩ => ?_
  have F : Frm I.B (prodRanges (vk I.k) y x a t) u.mem u'.mem := by
    intro z hz
    have hh := fun r (hr : r ∈ hdrW) => hz r (List.mem_append_left _ hr)
    have ry := hz (slot (vk I.k) y, 8 * vk I.k) (by simp)
    have rt := hz (slot (Wk I.k) t, 8 * Wk I.k) (by simp)
    have ra := hz (slot (Wk I.k) a, 8 * Wk I.k) (by simp)
    have rx := hz (slot (Wk I.k) x, 8 * Wk I.k) (by simp)
    dsimp only at ry rt ra rx
    rw [m', f₇ z hh, o₆ z rx, o₅ z ra, o₄ z rt, f₃ z hh, o₂ z ry, m₁]
  refine ⟨⟨g₇.same m' k₈ (by decide), ?_, ?_, hI.frm.trans F⟩, ?_⟩
  · rw [Function.iterate_succ_apply', ← hval, prodStep_val, m', Frm.hdrW_wv f₇ (slot_ge _ _) (by omega),
      Frm.hdrW_wv f₇ (slot_ge _ _) (by omega), Frm.hdrW_wv f₇ (slot_ge _ _) (by omega), v₆,
      o₆.wv (rd_sep (Ne.symm P.xa) (by omega) (by omega)) (by omega), v₅,
      o₆.wv (nw_sep P.yx1 P.yx2 (by omega) (by omega)) (by omega),
      o₅.wv (nw_sep P.ya1 P.ya2 (by omega) (by omega)) (by omega),
      o₄.wv (nw_sep P.yt1 P.yt2 (by omega) (by omega)) (by omega), Frm.hdrW_wv f₃ (slot_ge _ _) (by omega), v₂]
  · rw [m', Frm.hdrW_word f₇ (by have := slot_ge (vk I.k) y; omega) (by omega),
      o₆.word (wdw_sep P.yx1 P.yx2 (by omega) (by omega)) (by omega),
      o₅.word (wdw_sep P.ya1 P.ya2 (by omega) (by omega)) (by omega),
      o₄.word (wdw_sep P.yt1 P.yt2 (by omega) (by omega)) (by omega),
      Frm.hdrW_word f₃ (by have := slot_ge (vk I.k) y; omega) (by omega), o₂.word (.inr (by omega)) (by omega), m₁, hI.zY]
  · rw [h6, k₇.gpr .x6 (by decide), k₆.gpr .x6 (by decide), k₅.gpr .x6 (by decide), k₄.gpr .x6 (by decide),
      k₃.gpr .x6 (by decide), k₂.gpr .x6 (by decide), k₁.gpr .x6 (by decide)]

/-- `product y x a t`: `64 v` steps of `prodStep`. -/
theorem product_ok {I : RpIn} {m₀ : Mem} {c : Bool} {y x a t : Nat} {s : State} (h : G I m₀ (vk I.k) c s)
    (L : RpLens I) (P : PIdx y x a t) (hz : word s.mem I.B (slot (vk I.k) y + 8 * vk I.k) = 0) :
    WP isa (product y x a t) s (PI I m₀ c y x a t s (wv s.mem I.B (slot (vk I.k) y) (vk I.k),
      wv s.mem I.B (slot (Wk I.k) x) (Wk I.k), wv s.mem I.B (slot (Wk I.k) a) (Wk I.k)) (64 * vk I.k)) := by
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega
  have hv2 : vk I.k ≤ 200 := by have := L.k2; simp only [vk]; omega
  unfold product
  refine WP.seq (WP.mono (countN_ok h.ws) fun u ⟨⟨h6, mu⟩, ku⟩ => ?_)
  refine wp_countdown (N := 64 * vk I.k) (by omega) (by omega) _ (fun i _ u' hI _ => prodStepCode_ok L P hI)
    ⟨h.same mu ku (by decide), by rw [mu]; rfl, by rw [mu]; exact hz, by rw [mu]; exact Frm.refl _ _ _⟩ h6

/-- A wide array cleared and then given a narrow value has that value. -/
theorem wide_of_zero {B : Addr} {v i : Nat} {m m' : Mem} (hz : wv m B (slot (2 * v + 2) i) (2 * v + 4) = 0)
    (o : Outside B (slot v (2 * i)) (8 * v) m m') (hb : slot v (2 * i) + 8 * (2 * v + 4) ≤ 2 ^ 64) :
    wv m' B (slot (2 * v + 2) i) (2 * v + 2) = wv m' B (slot v (2 * i)) v := by
  rw [slot_wide, show 2 * v + 2 = v + (v + 2) by omega, wv_add,
    o.wv (.inr (Nat.le_refl _)) (by omega)]
  rw [slot_wide, show 2 * v + 4 = v + (v + 2 + 2) by omega, wv_add] at hz
  have e := wv_add m B (slot v (2 * i) + 8 * v) (v + 2) 2
  have : 2 ^ (64 * v) * wv m B (slot v (2 * i) + 8 * v) (v + 2 + 2) = 0 := by omega
  have := (Nat.mul_eq_zero.mp this).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos _))
  rw [e] at this
  have : wv m B (slot v (2 * i) + 8 * v) (v + 2) = 0 := by omega
  rw [this, Nat.mul_zero, Nat.add_zero]

end VG.Proof.Rsa.AArch64.Rd
