module
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Impl.Rsa.AArch64.CheckKeyCore

import VerifiedGarbage.Proof.Bignum.AArch64.CrtRows
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# `vg_rsa_check_key` on AArch64: the pieces

In the layout of `W = 2 w + 2` words: the mask of `[a] < [b]` (`ltA_ok`),
and the products `[aX] e` (`mulE_ok`) and `[aX] [aR]` (`mulXR_ok`) of
numbers below `2^(64 w)`, by rows of `w` words.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- `ws` and `x14 := W`, `x7 := 0` and the carry set. -/
theorem ltHead_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7])) s fun t =>
      (t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .x7 = 0 ∧
        t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = true ∧ t.mem = s.mem) ∧ Keep [.x3, .x7, .x11, .x12, .x14] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    h.scr.ld (by have := h.h256; omega_arith)
  refine WP.keep [.x3, .x7, .x11, .x12, .x14] ?_ (by decide) (by decide) (by decide +kernel)
  brun [ws, h.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sStride < 32 by decide),
    hl sW (by decide), hl sStride (by decide), h.hw, h.hS]

/-- `ltA a b`: the mask of `[a] < [b]` (over `w` words) and'ed into `sMask`. -/
theorem ltA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {a b : Nat} (ha : a < 16) (hb : b < 16)
    {c : Bool} (hm : word s.mem B (8 * Public.sMask) = mask c) :
    WP isa (seqs (ltA a b)) s fun t =>
      t.mem = s.mem.writeW (off B (8 * Public.sMask))
        (mask (decide (wv s.mem B (slot w a) w < wv s.mem B (slot w b) w) && c)) ∧
      Keep [.x3, .x4, .x7, .x11, .x12, .x14, .x15, .x16, .x17] s t := by
  have hn := h.scr.nowrap
  have sa := h.sl ha
  have sb := h.sl hb
  simp only [ltA, seqs]
  refine WP.seq (WP.mono (ltHead_ok h) fun s₁ ⟨⟨h12, h11, h7, h14, hc, m₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (base2_ok a b .x16 .x17 ((k₁.gpr .x0 (by decide)).trans h.x0) h11)
    fun s₂ ⟨⟨h16, h17, m₂, c₂⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.seq (WP.mono (cmpLoop_ok (h.scr.congr k12.wr) h16 h17 ((k₂.gpr .x14 (by decide)).trans h14)
    (c₂.trans hc) (by have := h.w1; omega_arith) (by have := h.w2; omega_arith) (by omega_arith) (by omega_arith))
    fun s₃ ⟨hc₃, m₃, k₃⟩ => ?_)
  rw [m₂, m₁] at hc₃
  have k13 := k12.trans k₃
  have hst := (h.scr.congr k13.wr).st (d := 8 * Public.sMask) (by have := h.h256; unfold Public.sMask sFn; omega_arith)
  have hld := (h.scr.congr k13.wr).ld (d := 8 * Public.sMask) (by have := h.h256; unfold Public.sMask sFn; omega_arith)
  refine WP.mono (WP.keep [.x3, .x4, .x15] (Q := fun t => t.mem = s.mem.writeW (off B (8 * Public.sMask))
      (mask (decide (wv s.mem B (slot w a) w < wv s.mem B (slot w b) w) && c))) (by
    brun [borrowMask, ((k₂.trans k₃).gpr .x7 (by decide)).trans h7, csel_mask_not, hc₃, Bool.not_not,
      (k13.gpr .x0 (by decide)).trans h.x0, hdr_enc (show Public.sMask < 32 by decide), hld, hst, m₃, m₂, m₁, hm,
      mask_and'])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨mt, k₄⟩ => ⟨mt, (k13.trans k₄).mono (by decide)⟩

/-- `narrow`: `w` from `2 w + 2`. -/
theorem narrow_val (w : Nat) (hw : 2 * w + 2 < 2 ^ 64) :
    (BitVec.ofNat 64 (2 * w + 2) - BitVec.ofNat 64 2) >>> 1 = BitVec.ofNat 64 w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega_arith

/-- Every register but `x0`. -/
def ckRegs : List Reg := [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- After `zeroA aA`: the working space, `[aA] = 0`, the rest unchanged. -/
theorem zeroAA_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W) :
    WP isa (zeroA aA) s fun t => Ws t B Z W ∧ wv t.mem B (slot W aA) (W + 2) = 0 ∧
      Outside B (slot W aA) (8 * (W + 2)) s.mem t.mem ∧ Keep ckRegs s t :=
  WP.mono (zeroA_ok h (j := aA) (by decide)) fun _ ⟨hz, o, _, _, _, k⟩ =>
    ⟨h.congr (Frm.of_outside o (List.mem_singleton_self _)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) k (by decide), hz, o, k.mono (by decide)⟩

/-- The words of `[aA]` above the product are still zero. -/
theorem wv_prod {m₀ m : Mem} {B : Addr} {W n : Nat} (hn : n ≤ W) (hz : wv m₀ B (slot W aA) (W + 2) = 0)
    (o : Outside B (slot W aA) (8 * n) m₀ m) (hB : (B.toNat) + slot W aA + 8 * (W + 2) ≤ 2 ^ 64) :
    wv m B (slot W aA) W = wv m B (slot W aA) n := by
  have hz' : ∀ q < W + 2, word m₀ B (slot W aA + 8 * q) = 0 := (wv_eq_zero_iff _ _ _ _).mp hz
  have e := wv_add m B (slot W aA) n (W - n)
  rw [show n + (W - n) = W by omega_arith] at e
  rw [e, wv_zero (n := W - n) fun q hq => by
    rw [o.word (by omega_arith) (by omega_arith), Nat.add_assoc, ← Nat.mul_add]; exact hz' _ (by omega_arith)]
  simp

theorem mulE_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z (2 * w + 2)) (hw1 : 1 ≤ w) {X : Nat}
    (hX : wv s.mem B (slot (2 * w + 2) aX) (2 * w + 2) = X) (hXl : X < 2 ^ (64 * w)) :
    WP isa (seqs mulE) s fun t =>
      wv t.mem B (slot (2 * w + 2) aA) (2 * w + 2) = X * (word s.mem B (slot (2 * w + 2) aE)).toNat ∧
      Outside B (slot (2 * w + 2) aA) (8 * (2 * w + 2 + 2)) s.mem t.mem ∧ Keep ckRegs s t := by
  have hn := h.scr.nowrap
  have hw2 := h.w2
  have sA := h.sl (j := aA) (by decide)
  have sX := h.sl (j := aX) (by decide)
  have sE := h.sl (j := aE) (by decide)
  have pAX := slot_sep (w := 2 * w + 2) (show aA ≠ aX by decide)
  have pAE := slot_sep (w := 2 * w + 2) (show aA ≠ aE by decide)
  simp only [mulE, seqs]
  refine WP.seq (WP.mono (zeroAA_ok h) fun s₁ ⟨h₁, hz, o₁, k₁⟩ => ?_)
  have eX : wv s₁.mem B (slot (2 * w + 2) aX) (2 * w + 2) = X := by rw [o₁.wv (by omega_arith) (by omega_arith), hX]
  have eE : word s₁.mem B (slot (2 * w + 2) aE) = word s.mem B (slot (2 * w + 2) aE) :=
    o₁.word (by omega_arith) (by omega_arith)
  have e : ws ++ base aE .x1 ++ base aX .x9 ++ base aA .x8 ++ [ld .x1 .x1] ++ narrow ++ [movi .x7 0] =
      ws ++ ((base aE .x1 ++ base aX .x9 ++ base aA .x8) ++ ([ld .x1 .x1] ++ narrow ++ [movi .x7 0])) := by
    simp only [List.append_assoc]
  rw [e]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h₁.ws_ok fun s₂ ⟨⟨h12, h11, m₂, _⟩, k₂⟩ =>
    WP.block_append_iff.mpr (WP.mono (base3_ok aE aX aA .x1 .x9 .x8 ((k₂.gpr .x0 (by decide)).trans h₁.x0) h11)
      fun s₃ ⟨⟨h1, h9, h8, m₃, _⟩, k₃⟩ => ?_)))
  have hs₃ := h₁.scr.congr (k₂.trans k₃).wr
  refine WP.mono (WP.keep [.x1, .x12, .x7] (Q := fun t => t.gpr .x1 = word s.mem B (slot (2 * w + 2) aE) ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧ t.mem = s₃.mem) (by
    brun [narrow, h1, (k₃.gpr .x12 (by decide)).trans h12, hs₃.ld (d := slot (2 * w + 2) aE) (by omega_arith), m₃, m₂,
      eE, narrow_val w (by omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun s₄ ⟨⟨h1₄, h12₄, h7₄, m₄⟩, k₄⟩ => ?_
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have eX₄ : wv s₄.mem B (slot (2 * w + 2) aX) w = X := by
    rw [m₄, m₃, m₂, wv_low_of_lt (v := w) (w := 2 * w + 2) (by omega_arith) (by rw [eX]; exact hXl), eX]
  have eA₄ : wv s₄.mem B (slot (2 * w + 2) aA) (w + 2) = 0 := by
    rw [m₄, m₃, m₂]
    have := wv_add s₁.mem B (slot (2 * w + 2) aA) (w + 2) (w + 2)
    rw [show w + 2 + (w + 2) = 2 * w + 2 + 2 by omega_arith, hz] at this
    omega_arith
  have he := (word s.mem B (slot (2 * w + 2) aE)).isLt
  refine WP.mono (mulAddRow_ok (h.scr.congr k14.wr) ((k₄.gpr .x8 (by decide)).trans h8)
    ((k₄.gpr .x9 (by decide)).trans h9) h12₄ h7₄ hw1 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by
      rw [eA₄, eX₄, h1₄, Nat.zero_add]
      calc (word s.mem B (slot (2 * w + 2) aE)).toNat * X < 2 ^ 64 * 2 ^ (64 * w) :=
            Nat.mul_lt_mul_of_lt_of_le he (Nat.le_of_lt hXl) (Nat.two_pow_pos _)
        _ ≤ 2 ^ (64 * (w + 2)) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega_arith)))
    fun t ⟨hv, o, k₅⟩ => ?_
  have o' : Outside B (slot (2 * w + 2) aA) (8 * (2 * w + 2 + 2)) s.mem t.mem := fun x hx => by
    rw [o x (by omega_arith), m₄, m₃, m₂]; exact o₁ x hx
  refine ⟨?_, o', (k14.trans k₅).mono (by decide)⟩
  have hz₁ : wv s₄.mem B (slot (2 * w + 2) aA) (2 * w + 2 + 2) = 0 := by rw [m₄, m₃, m₂, hz]
  rw [wv_prod (n := w + 2) (by omega_arith) hz₁ (o.mono (Nat.le_refl _) (Nat.le_refl _)) (by omega_arith), hv, eA₄, eX₄, h1₄,
    Nat.zero_add, Nat.mul_comm]

theorem mulXR_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z (2 * w + 2)) (hw1 : 1 ≤ w) {X R : Nat}
    (hX : wv s.mem B (slot (2 * w + 2) aX) (2 * w + 2) = X) (hXl : X < 2 ^ (64 * w))
    (hR : wv s.mem B (slot (2 * w + 2) aR) (2 * w + 2) = R) (hRl : R < 2 ^ (64 * w)) :
    WP isa (seqs mulXR) s fun t =>
      wv t.mem B (slot (2 * w + 2) aA) (2 * w + 2) = X * R ∧
      Outside B (slot (2 * w + 2) aA) (8 * (2 * w + 2 + 2)) s.mem t.mem ∧ Keep ckRegs s t := by
  have hn := h.scr.nowrap
  have hw2 := h.w2
  have sA := h.sl (j := aA) (by decide)
  have sX := h.sl (j := aX) (by decide)
  have sR := h.sl (j := aR) (by decide)
  have pAX := slot_sep (w := 2 * w + 2) (show aA ≠ aX by decide)
  have pAR := slot_sep (w := 2 * w + 2) (show aA ≠ aR by decide)
  simp only [mulXR, seqs]
  refine WP.seq (WP.mono (zeroAA_ok h) fun s₁ ⟨h₁, hz, o₁, k₁⟩ => ?_)
  have eX : wv s₁.mem B (slot (2 * w + 2) aX) (2 * w + 2) = X := by rw [o₁.wv (by omega_arith) (by omega_arith), hX]
  have eR : wv s₁.mem B (slot (2 * w + 2) aR) (2 * w + 2) = R := by rw [o₁.wv (by omega_arith) (by omega_arith), hR]
  have e : ws ++ base aX .x5 ++ base aR .x9 ++ base aA .x8 ++ [mov .x11 .x5] ++ narrow ++
      [mov .x13 .x12, movi .x7 0] =
      ws ++ ((base aX .x5 ++ base aR .x9 ++ base aA .x8) ++ ([mov .x11 .x5] ++ narrow ++
        [mov .x13 .x12, movi .x7 0])) := by
    simp only [List.append_assoc]
  rw [e]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h₁.ws_ok fun s₂ ⟨⟨h12, h11, m₂, _⟩, k₂⟩ =>
    WP.block_append_iff.mpr (WP.mono (base3_ok aX aR aA .x5 .x9 .x8 ((k₂.gpr .x0 (by decide)).trans h₁.x0) h11)
      fun s₃ ⟨⟨h5, h9, h8, m₃, _⟩, k₃⟩ => ?_)))
  refine WP.mono (WP.keep [.x11, .x12, .x13, .x7] (Q := fun t => t.gpr .x11 = off B (slot (2 * w + 2) aX) ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x13 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧ t.mem = s₃.mem) (by
    brun [narrow, h5, (k₃.gpr .x12 (by decide)).trans h12, narrow_val w (by omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun s₄ ⟨⟨h11₄, h12₄, h13₄, h7₄, m₄⟩, k₄⟩ => ?_
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have eX₄ : wv s₄.mem B (slot (2 * w + 2) aX) w = X := by
    rw [m₄, m₃, m₂, wv_low_of_lt (v := w) (w := 2 * w + 2) (by omega_arith) (by rw [eX]; exact hXl), eX]
  have eR₄ : wv s₄.mem B (slot (2 * w + 2) aR) w = R := by
    rw [m₄, m₃, m₂, wv_low_of_lt (v := w) (w := 2 * w + 2) (by omega_arith) (by rw [eR]; exact hRl), eR]
  have hz₁ : wv s₄.mem B (slot (2 * w + 2) aA) (2 * w + 2 + 2) = 0 := by rw [m₄, m₃, m₂, hz]
  have eA₄ : wv s₄.mem B (slot (2 * w + 2) aA) (w + w + 2) = 0 := by
    have := wv_add s₄.mem B (slot (2 * w + 2) aA) (w + w + 2) 2
    rw [show w + w + 2 + 2 = 2 * w + 2 + 2 by omega_arith, hz₁] at this
    omega_arith
  refine WP.mono (mulRows_ok (wa := w) (wb := w) (h.scr.congr k14.wr) h11₄ ((k₄.gpr .x9 (by decide)).trans h9)
    h13₄ h12₄ ((k₄.gpr .x8 (by decide)).trans h8) h7₄ hw1 hw1 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by rw [eA₄]; exact Nat.two_pow_pos _)) fun t ⟨hv, o, k₅⟩ => ?_
  have o' : Outside B (slot (2 * w + 2) aA) (8 * (2 * w + 2 + 2)) s.mem t.mem := fun x hx => by
    rw [o x (by omega_arith), m₄, m₃, m₂]; exact o₁ x hx
  refine ⟨?_, o', (k14.trans k₅).mono (by decide)⟩
  refine (congrArg (wv t.mem B (slot (2 * w + 2) aA)) (show 2 * w + 2 = w + w + 2 by omega_arith)).trans ?_
  rw [hv, eA₄, eX₄, eR₄, Nat.zero_add]

/-- `mulPQ`'s setup: the bases, and `⌈q_len / 8⌉` and `⌈p_len / 8⌉` from the header. -/
theorem pqSetupK_ok {s : State} {B : Addr} {Z w pl ql : Nat} (h : Ws s B Z (2 * w + 2))
    (hpl : word s.mem B (8 * sPlen) = BitVec.ofNat 64 pl) (hql : word s.mem B (8 * sQlen) = BitVec.ofNat 64 ql)
    (pb : pl < 2 ^ 60) (qb : ql < 2 ^ 60) :
    WP isa (.block (ws ++ base aX .x5 ++ base aR .x9 ++ base aA .x8 ++ [mov .x11 .x5, ldh .x12 sQlen,
      .addImm .x .x12 .x12 7, .lsr .x .x12 .x12 3, ldh .x13 sPlen, .addImm .x .x13 .x13 7, .lsr .x .x13 .x13 3,
      movi .x7 0])) s fun t =>
      t.gpr .x0 = B ∧ t.gpr .x11 = off B (slot (2 * w + 2) aX) ∧ t.gpr .x9 = off B (slot (2 * w + 2) aR) ∧
      t.gpr .x8 = off B (slot (2 * w + 2) aA) ∧ t.gpr .x12 = BitVec.ofNat 64 ((ql + 7) / 8) ∧
      t.gpr .x13 = BitVec.ofNat 64 ((pl + 7) / 8) ∧ t.gpr .x7 = 0 := by
  have hn := h.scr.nowrap
  have hw2 := h.w2
  have hZ := h.hZ
  have := hdr_lt_slot (2 * w + 2) 16 (show 31 < 32 by decide)
  have e : ws ++ base aX .x5 ++ base aR .x9 ++ base aA .x8 ++ [mov .x11 .x5, ldh .x12 sQlen,
      .addImm .x .x12 .x12 7, .lsr .x .x12 .x12 3, ldh .x13 sPlen, .addImm .x .x13 .x13 7, .lsr .x .x13 .x13 3,
      movi .x7 0] =
      ws ++ ((base aX .x5 ++ base aR .x9 ++ base aA .x8) ++ [mov .x11 .x5, ldh .x12 sQlen,
      .addImm .x .x12 .x12 7, .lsr .x .x12 .x12 3, ldh .x13 sPlen, .addImm .x .x13 .x13 7, .lsr .x .x13 .x13 3,
      movi .x7 0]) := by
    simp only [List.append_assoc]
  rw [e]
  refine WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨⟨h12, h11, m₂, _⟩, k₂⟩ =>
    WP.block_append_iff.mpr (WP.mono (base3_ok aX aR aA .x5 .x9 .x8 ((k₂.gpr .x0 (by decide)).trans h.x0) h11)
      fun s₃ ⟨⟨h5, h9, h8, m₃, _⟩, k₃⟩ => ?_))
  have k13 := k₂.trans k₃
  have hs₃ := h.scr.congr k13.wr
  have hl : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi => hs₃.ld (by omega_arith)
  have mm : s₃.mem = s.mem := by rw [m₃, m₂]
  refine WP.mono (WP.keep [.x11, .x12, .x13, .x7] (Q := fun t => t.gpr .x11 = off B (slot (2 * w + 2) aX) ∧
      t.gpr .x12 = BitVec.ofNat 64 ((ql + 7) / 8) ∧ t.gpr .x13 = BitVec.ofNat 64 ((pl + 7) / 8) ∧
      t.gpr .x7 = 0) (by
    brun [(k13.gpr .x0 (by decide)).trans h.x0, h5, hdr_enc (show sQlen < 32 by decide),
      hdr_enc (show sPlen < 32 by decide), hl sQlen (by decide), hl sPlen (by decide), mm, hpl, hql,
      ceil8_bv pb, ceil8_bv qb])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h11', h12', h13', h7'⟩, k₄⟩ => ?_
  exact ⟨(k₄.gpr .x0 (by decide)).trans ((k13.gpr .x0 (by decide)).trans h.x0), h11',
    (k₄.gpr .x9 (by decide)).trans h9, (k₄.gpr .x8 (by decide)).trans h8, h12', h13', h7'⟩

/-- `mulPQ`: `[aA] := [aX] [aR]` over their `⌈p_len / 8⌉` and `⌈q_len / 8⌉` words. -/
theorem mulPQ_raw_ok {s : State} {B : Addr} {Z w pl ql : Nat} (h : Ws s B Z (2 * w + 2))
    (hpl : word s.mem B (8 * sPlen) = BitVec.ofNat 64 pl) (hql : word s.mem B (8 * sQlen) = BitVec.ofNat 64 ql)
    (pl1 : 1 ≤ pl) (ql1 : 1 ≤ ql) (hpw : (pl + 7) / 8 ≤ w) (hqw : (ql + 7) / 8 ≤ w) :
    WP isa (seqs mulPQ) s fun t =>
      wv t.mem B (slot (2 * w + 2) aA) (2 * w + 2) =
        wv s.mem B (slot (2 * w + 2) aX) ((pl + 7) / 8) * wv s.mem B (slot (2 * w + 2) aR) ((ql + 7) / 8) ∧
      Outside B (slot (2 * w + 2) aA) (8 * (2 * w + 2 + 2)) s.mem t.mem ∧ Keep ckRegs s t := by
  have hn := h.scr.nowrap
  have hw2 := h.w2
  have sA := h.sl (j := aA) (by decide)
  have sX := h.sl (j := aX) (by decide)
  have sR := h.sl (j := aR) (by decide)
  have pAX := slot_sep (w := 2 * w + 2) (show aA ≠ aX by decide)
  have pAR := slot_sep (w := 2 * w + 2) (show aA ≠ aR by decide)
  have hA8 : 8 * 32 ≤ slot (2 * w + 2) aA := by have := hdr_lt_slot (2 * w + 2) aA (show 31 < 32 by decide); omega_arith
  simp only [mulPQ, seqs]
  refine WP.seq (WP.mono (zeroAA_ok h) fun s₁ ⟨h₁, hz, o₁, k₁⟩ => ?_)
  have eX : wv s₁.mem B (slot (2 * w + 2) aX) ((pl + 7) / 8) = wv s.mem B (slot (2 * w + 2) aX) ((pl + 7) / 8) :=
    o₁.wv (by omega_arith) (by omega_arith)
  have eR : wv s₁.mem B (slot (2 * w + 2) aR) ((ql + 7) / 8) = wv s.mem B (slot (2 * w + 2) aR) ((ql + 7) / 8) :=
    o₁.wv (by omega_arith) (by omega_arith)
  have hpl₁ : word s₁.mem B (8 * sPlen) = BitVec.ofNat 64 pl := by
    rw [o₁.word (Or.inl (by unfold sPlen sFn; omega_arith)) (by unfold sPlen sFn; omega_arith)]; exact hpl
  have hql₁ : word s₁.mem B (8 * sQlen) = BitVec.ofNat 64 ql := by
    rw [o₁.word (Or.inl (by unfold sQlen sFn; omega_arith)) (by unfold sQlen sFn; omega_arith)]; exact hql
  have e : ws ++ base aX .x5 ++ base aR .x9 ++ base aA .x8 ++ [mov .x11 .x5, ldh .x12 sQlen,
      .addImm .x .x12 .x12 7, .lsr .x .x12 .x12 3, ldh .x13 sPlen, .addImm .x .x13 .x13 7, .lsr .x .x13 .x13 3,
      movi .x7 0] =
      ws ++ ((base aX .x5 ++ base aR .x9 ++ base aA .x8) ++ [mov .x11 .x5, ldh .x12 sQlen,
      .addImm .x .x12 .x12 7, .lsr .x .x12 .x12 3, ldh .x13 sPlen, .addImm .x .x13 .x13 7, .lsr .x .x13 .x13 3,
      movi .x7 0]) := by
    simp only [List.append_assoc]
  rw [e]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h₁.ws_ok fun s₂ ⟨⟨h12, h11, m₂, _⟩, k₂⟩ =>
    WP.block_append_iff.mpr (WP.mono (base3_ok aX aR aA .x5 .x9 .x8 ((k₂.gpr .x0 (by decide)).trans h₁.x0) h11)
      fun s₃ ⟨⟨h5, h9, h8, m₃, _⟩, k₃⟩ => ?_)))
  have k13 := (k₂.trans k₃)
  have hs₃ := h₁.scr.congr k13.wr
  have hl : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi => hs₃.ld (by omega_arith)
  have mm : s₃.mem = s₁.mem := by rw [m₃, m₂]
  refine WP.mono (WP.keep [.x11, .x12, .x13, .x7] (Q := fun t => t.gpr .x11 = off B (slot (2 * w + 2) aX) ∧
      t.gpr .x12 = BitVec.ofNat 64 ((ql + 7) / 8) ∧ t.gpr .x13 = BitVec.ofNat 64 ((pl + 7) / 8) ∧
      t.gpr .x7 = 0 ∧ t.mem = s₃.mem) (by
    brun [(k13.gpr .x0 (by decide)).trans h₁.x0, h5, hdr_enc (show sQlen < 32 by decide),
      hdr_enc (show sPlen < 32 by decide), hl sQlen (by decide), hl sPlen (by decide), mm, hpl₁, hql₁,
      ceil8_bv (show pl < 2 ^ 60 by omega_arith), ceil8_bv (show ql < 2 ^ 60 by omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun s₄ ⟨⟨h11₄, h12₄, h13₄, h7₄, m₄⟩, k₄⟩ => ?_
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  generalize hwp' : (pl + 7) / 8 = wp at *
  generalize hwq' : (ql + 7) / 8 = wq at *
  have hz₁ : wv s₄.mem B (slot (2 * w + 2) aA) (2 * w + 2 + 2) = 0 := by rw [m₄, m₃, m₂, hz]
  have hz' := (wv_eq_zero_iff _ _ _ _).mp hz₁
  have eA₄ : wv s₄.mem B (slot (2 * w + 2) aA) (wp + wq + 2) = 0 :=
    (wv_eq_zero_iff _ _ _ _).mpr fun i hi => hz' i (by omega_arith)
  refine WP.mono (mulRows_ok (wa := wp) (wb := wq) (h.scr.congr k14.wr) h11₄ ((k₄.gpr .x9 (by decide)).trans h9)
    h13₄ h12₄ ((k₄.gpr .x8 (by decide)).trans h8) h7₄ (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [eA₄]; exact Nat.two_pow_pos _)) fun t ⟨hv, o, k₅⟩ => ?_
  have o' : Outside B (slot (2 * w + 2) aA) (8 * (2 * w + 2 + 2)) s.mem t.mem := fun x hx => by
    rw [o x (by omega_arith), m₄, m₃, m₂]; exact o₁ x hx
  refine ⟨?_, o', (k14.trans k₅).mono (by decide)⟩
  have e := wv_add t.mem B (slot (2 * w + 2) aA) (wp + wq + 2) (2 * w + 2 - (wp + wq + 2))
  have z : wv t.mem B (slot (2 * w + 2) aA + 8 * (wp + wq + 2)) (2 * w + 2 - (wp + wq + 2)) = 0 :=
    (wv_eq_zero_iff _ _ _ _).mpr fun i hi => by
      rw [o.word (by omega_arith) (by omega_arith),
        show slot (2 * w + 2) aA + 8 * (wp + wq + 2) + 8 * i = slot (2 * w + 2) aA + 8 * (wp + wq + 2 + i) by
          omega_arith]
      exact hz' _ (by omega_arith)
  rw [show wp + wq + 2 + (2 * w + 2 - (wp + wq + 2)) = 2 * w + 2 by omega_arith, z, Nat.mul_zero, Nat.add_zero,
    hv, eA₄, Nat.zero_add, m₄, m₃, m₂, eX, eR] at e
  exact e

/-- `mulPQ`: `[aA] := [aX] [aR]`, for `[aX] < 256^p_len` and `[aR] < 256^q_len`. -/
theorem mulPQ_ok {s : State} {B : Addr} {Z w pl ql : Nat} (h : Ws s B Z (2 * w + 2))
    (hpl : word s.mem B (8 * sPlen) = BitVec.ofNat 64 pl) (hql : word s.mem B (8 * sQlen) = BitVec.ofNat 64 ql)
    (pl1 : 1 ≤ pl) (ql1 : 1 ≤ ql) (hpw : (pl + 7) / 8 ≤ w) (hqw : (ql + 7) / 8 ≤ w) {X R : Nat}
    (hX : wv s.mem B (slot (2 * w + 2) aX) (2 * w + 2) = X) (hXl : X < 256 ^ pl)
    (hR : wv s.mem B (slot (2 * w + 2) aR) (2 * w + 2) = R) (hRl : R < 256 ^ ql) :
    WP isa (seqs mulPQ) s fun t =>
      wv t.mem B (slot (2 * w + 2) aA) (2 * w + 2) = X * R ∧
      Outside B (slot (2 * w + 2) aA) (8 * (2 * w + 2 + 2)) s.mem t.mem ∧ Keep ckRegs s t := by
  have lt : ∀ {Y l : Nat}, Y < 256 ^ l → Y < 2 ^ (64 * ((l + 7) / 8)) := fun {Y l} hY =>
    Nat.lt_of_lt_of_le hY (by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega))
  refine WP.mono (mulPQ_raw_ok h hpl hql pl1 ql1 hpw hqw) fun t ⟨hv, o, k⟩ => ⟨?_, o, k⟩
  rw [hv, wv_low_of_lt (v := (pl + 7) / 8) (w := 2 * w + 2) (by omega) (by rw [hX]; exact lt hXl), hX,
    wv_low_of_lt (v := (ql + 7) / 8) (w := 2 * w + 2) (by omega) (by rw [hR]; exact lt hRl), hR]

end VG.Proof.Rsa.AArch64
