import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.State
import VerifiedGarbage.Proof.Rsa.AArch64.CkPieces
import VerifiedGarbage.Proof.Rsa.AArch64.Inv

/-!
# An RSA key from its primes on AArch64: the pieces

The routines the code is made of, from `KS`: what each leaves in the arrays
(`av`, the low `W` words of one) and in the registers, and the parts it
changes (`KF`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- A zero number of `W + 2` words: its low `W` words and word `W`. -/
theorem wv_zero2 {m : Mem} {B : Addr} {d W : Nat} (hz : wv m B d (W + 2) = 0) :
    wv m B d W = 0 ∧ word m B (d + 8 * W) = 0 := by
  have := (wv_eq_zero_iff _ _ _ _).mp hz
  exact ⟨wv_zero fun k hk => this k (by omega), this W (by omega)⟩

/-- Word `k` of a zero number written. -/
theorem wv_put {m : Mem} {B : Addr} {d N k : Nat} (v : BitVec 64) (hz : ∀ q < N, word m B (d + 8 * q) = 0)
    (hd : d + 8 * N ≤ 2 ^ 64) (hk : k < N) : ∀ n ≤ N,
    wv (m.writeW (off B (d + 8 * k)) v) B d n = if k < n then 2 ^ (64 * k) * v.toNat else 0
  | 0, _ => by simp [wv]
  | n + 1, hn => by
    rw [wv, wv_put v hz hd hk n (by omega)]
    by_cases hkn : n = k
    · subst hkn; rw [word_writeW_self]; simp
    · rw [(writeW_outside m B v (d := d + 8 * k) (by omega)).word (by omega) (by omega), hz n (by omega)]
      by_cases hk' : k < n
      · simp [hk', show k < n + 1 by omega]
      · simp [hk', show ¬ k < n + 1 by omega]

/-- A zero number of `W + 2` words with its low word set to `v`. -/
theorem wv_put0 {m : Mem} {B : Addr} {d W : Nat} (v : BitVec 64) (hz : wv m B d (W + 2) = 0)
    (hd : d + 8 * (W + 2) ≤ 2 ^ 64) : wv (m.writeW (off B d) v) B d (W + 2) = v.toNat := by
  have := wv_put (m := m) (B := B) (d := d) (N := W + 2) (k := 0) v ((wv_eq_zero_iff _ _ _ _).mp hz) hd
    (by omega) (W + 2) (Nat.le_refl _)
  rw [Nat.mul_zero, Nat.add_zero] at this
  rw [this, ite_eq_left (show 0 < W + 2 by omega), Nat.pow_zero, Nat.one_mul]

/-! ## Clearing and copying -/

/-- `zeroA j`: `[j] := 0` (`W + 2` words). -/
theorem zeroA_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {j : Nat} (hj : j < 16) :
    WP isa (zeroA j) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr j] s.mem t.mem ∧
      wv t.mem I.B (slot I.W j) (I.W + 2) = 0 ∧ t.gpr .x7 = 0 ∧ Keep [.x11, .x12, .x8, .x7, .x14, .x16] s t :=
  WP.mono (zeroA_ok h.ws hj) fun t ⟨hz, o, _, _, h7, k⟩ =>
    have f := KF.arr1 o (Nat.le_refl _) (Nat.le_refl _)
    ⟨h.step f (all_mut_arr hj) k, f, hz, h7, k⟩

/-- `copyA o a`: `[o] := [a]` over `W` words. -/
theorem copyA_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {o a : Nat} (ho : o < 16) (ha : a < 16)
    (hoa : o ≠ a) :
    WP isa (copyA o a) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr o] s.mem t.mem ∧
      av I t.mem o = av I s.mem a ∧ atop I t.mem o = atop I s.mem o ∧
      Keep [.x11, .x12, .x3, .x14, .x16, .x17] s t :=
  WP.mono (copyA_ok h.ws ho ha hoa) fun t ⟨hv, o', _, _, k⟩ =>
    have f := KF.arr1 o' (Nat.le_refl _) (by omega)
    have hn := h.ws.scr.nowrap
    have := h.ws.sl ho
    ⟨h.step f (all_mut_arr ho) k, f, hv, o'.word (Or.inr (Nat.le_refl _)) (by omega), k⟩

/-- `zeroA` then `copyA`: `[o] := [a]` with words `W` and `W + 1` zero. -/
theorem zc_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {o a : Nat} (ho : o < 16) (ha : a < 16)
    (hoa : o ≠ a) :
    WP isa (seqs [zeroA o, copyA o a]) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr o] s.mem t.mem ∧
      av I t.mem o = av I s.mem a ∧ atop I t.mem o = 0 := by
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h ho) fun s₁ ⟨h₁, f₁, z₁, _, _⟩ => ?_)
  refine WP.mono (copyA_k h₁ ho ha hoa) fun t ⟨ht, f₂, v₂, t₂, _⟩ => ⟨ht, ?_, ?_, ?_⟩
  · exact (f₁.trans f₂).mono (by simp)
  · rw [v₂]; exact f₁.arr (by simp [Rc.ok, ho]) ha (by simp [hoa.symm]) h.hZ
  · rw [t₂]; exact (wv_zero2 z₁).2

/-- `constA x`: `[aC] := x` over `W + 2` words. -/
theorem constA_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {x : Nat} (hx : x < 2 ^ 16) :
    WP isa (seqs (constA x)) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aC] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aC) (I.W + 2) = x ∧ Keep [.x11, .x12, .x8, .x7, .x14, .x16, .x3] s t := by
  have hn := h.ws.scr.nowrap
  have sC := h.ws.sl (j := aC) (by decide)
  simp only [constA, seqs]
  refine WP.seq (WP.mono (zeroA_k h (j := aC) (by decide)) fun s₁ ⟨h₁, f₁, z₁, _, k₁⟩ => ?_)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h₁.ws.ws_ok fun s₂ ⟨⟨_, h11, m₂, _⟩, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aC .x16 ((k₂.gpr .x0 (by decide)).trans h₁.ws.x0) h11) fun s₃ ⟨⟨h16, m₃, _⟩, k₃⟩ => ?_
  have hs₃ := h₁.ws.scr.congr (k₂.trans k₃).wr
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s₁.mem.writeW (off I.B (slot I.W aC))
      ((BitVec.ofNat 16 x).setWidth 64)) (by
    brun [h16, hs₃.st (d := slot I.W aC) (by omega), m₃, m₂]) rfl rfl rfl)
    fun t ⟨hm, k₄⟩ => ?_
  have o₄ := writeW_outside s₁.mem I.B ((BitVec.ofNat 16 x).setWidth 64) (d := slot I.W aC) (by omega)
  rw [← hm] at o₄
  have f₄ := KF.arr1 (j := aC) o₄ (Nat.le_refl _) (by omega)
  have kk := (k₂.trans k₃).trans k₄
  refine ⟨h₁.step f₄ (all_mut_arr (by decide)) kk, (f₁.trans f₄).mono (by simp), ?_,
    (k₁.trans kk).mono (by simp)⟩
  rw [hm, wv_put0 _ z₁ (by omega), BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
  exact Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide))

/-! ## Comparisons and masks -/

theorem not_decide_lt (a b : Nat) : (!decide (a < b)) = decide (b ≤ a) := by
  by_cases h : a < b
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

/-- `cmpA a b`: the carry flag clear iff `[a] < [b]` over `W` words. -/
theorem cmpA_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {a b : Nat} (ha : a < 16) (hb : b < 16) :
    WP isa (seqs (cmpA a b)) s fun t => KS I s₀ t ∧ t.mem = s.mem ∧
      t.c = !decide (av I s.mem a < av I s.mem b) ∧ t.gpr .x7 = 0 ∧ t.gpr .x12 = BitVec.ofNat 64 I.W ∧
      t.gpr .x11 = BitVec.ofNat 64 (8 * (I.W + 2)) ∧ Keep [.x3, .x4, .x7, .x11, .x12, .x14, .x16, .x17] s t := by
  have hn := h.ws.scr.nowrap
  have sa := h.ws.sl ha
  have sb := h.ws.sl hb
  simp only [cmpA, seqs]
  rw [show ws ++ ([movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] : List Instr) ++ base a .x16 ++ base b .x17 =
    (ws ++ ([movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] : List Instr)) ++ (base a .x16 ++ base b .x17) by
      simp only [List.append_assoc]]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (ltHead_ok h.ws) fun s₁ ⟨⟨h12, h11, h7, h14, hc, m₁⟩, k₁⟩ =>
    WP.mono (base2_ok a b .x16 .x17 ((k₁.gpr .x0 (by decide)).trans h.ws.x0) h11)
      fun s₂ ⟨⟨h16, h17, m₂, c₂⟩, k₂⟩ => ?_))
  have k12 := k₁.trans k₂
  refine WP.mono (cmpLoop_ok (h.ws.scr.congr k12.wr) h16 h17 ((k₂.gpr .x14 (by decide)).trans h14)
    (c₂.trans hc) (by have := h.ws.w1; omega) (by have := h.ws.w2; omega) (by omega) (by omega))
    fun t ⟨hc₃, m₃, k₃⟩ => ?_
  rw [m₂, m₁] at hc₃
  have kk := k12.trans k₃
  have k23 := k₂.trans k₃
  exact ⟨h.regs (by rw [m₃, m₂, m₁]) kk, by rw [m₃, m₂, m₁], hc₃, (k23.gpr .x7 (by decide)).trans h7,
    (k23.gpr .x12 (by decide)).trans h12, (k23.gpr .x11 (by decide)).trans h11, kk.mono (by decide)⟩

/-- `ltA a b`: `x15 := ` the mask of `[a] < [b]`. -/
theorem ltA_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {a b : Nat} (ha : a < 16) (hb : b < 16) :
    WP isa (seqs (ltA a b)) s fun t => KS I s₀ t ∧ t.mem = s.mem ∧
      t.gpr .x15 = mask (decide (av I s.mem a < av I s.mem b)) ∧ t.gpr .x7 = 0 ∧
      Keep [.x3, .x4, .x7, .x11, .x12, .x14, .x15, .x16, .x17] s t := by
  unfold ltA
  refine wp_seqs_append (by simp [cmpA]) (by simp) (WP.mono (cmpA_k h ha hb) fun s₁ ⟨h₁, m₁, c₁, h7, _, _, k₁⟩ => ?_)
  simp only [seqs]
  refine WP.mono (borrowMask_ok s₁ h7) fun t ⟨⟨h15, m₂, _⟩, k₂⟩ => ?_
  rw [c₁, Bool.not_not] at h15
  exact ⟨h₁.regs m₂ k₂, by rw [m₂, m₁], h15, (k₂.gpr .x7 (by decide)).trans h7, (k₁.trans k₂).mono (by decide)⟩

/-- `geA a b`: `x15 := ` the mask of `[a] ≥ [b]`. -/
theorem geA_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {a b : Nat} (ha : a < 16) (hb : b < 16) :
    WP isa (seqs (geA a b)) s fun t => KS I s₀ t ∧ t.mem = s.mem ∧
      t.gpr .x15 = mask (decide (av I s.mem b ≤ av I s.mem a)) ∧ t.gpr .x7 = 0 ∧
      Keep [.x3, .x4, .x7, .x11, .x12, .x14, .x15, .x16, .x17] s t := by
  unfold geA
  refine wp_seqs_append (by simp [cmpA]) (by simp) (WP.mono (cmpA_k h ha hb) fun s₁ ⟨h₁, m₁, c₁, h7, _, _, k₁⟩ => ?_)
  simp only [seqs]
  refine WP.mono (carryMask_ok s₁ h7) fun t ⟨⟨h15, m₂, _⟩, k₂⟩ => ?_
  rw [c₁, not_decide_lt] at h15
  exact ⟨h₁.regs m₂ k₂, by rw [m₂, m₁], h15, (k₂.gpr .x7 (by decide)).trans h7, (k₁.trans k₂).mono (by decide)⟩

/-- The value `carryMask` selects. -/
theorem csel_mask_c (c : Bool) :
    (if c then BitVec.setWidth 64 (0#16) - 1#64 else BitVec.setWidth 64 (0#16)) = mask c := by
  cases c <;> rfl

/-- `zeroMask`: `x15 := ` the mask of `x9 = 0`. -/
theorem zeroMask_ok (s : State) :
    WP isa (.block zeroMask) s fun t =>
      (t.gpr .x15 = mask (decide (s.gpr .x9 = 0)) ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem) ∧ Keep [.x3, .x4, .x7, .x15] s t := by
  refine WP.keep [.x3, .x4, .x7, .x15] ?_ (by decide) (by decide) (by decide +kernel)
  brun [zeroMask, borrowMask, Bool.toNat_true, csel_mask', lt_one_flag]

/-- `nonzeroMask`: `x15 := ` the mask of `x9 ≠ 0`. -/
theorem nonzeroMask_ok (s : State) :
    WP isa (.block nonzeroMask) s fun t =>
      (t.gpr .x15 = mask (!decide (s.gpr .x9 = 0)) ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem) ∧
        Keep [.x3, .x4, .x7, .x15] s t := by
  have e : decide (2 ^ 64 ≤ (s.gpr .x9).toNat + (~~~(BitVec.setWidth 64 1#16 : BitVec 64)).toNat + 1) =
      !decide (s.gpr .x9 = 0) := by
    rw [← lt_one_flag, Bool.not_not]
  refine WP.keep [.x3, .x4, .x7, .x15] ?_ (by decide) (by decide) (by decide +kernel)
  brun [nonzeroMask, carryMask, Bool.toNat_true, csel_mask_c, e]

/-- `eqMask a b`: `x15 := ` the mask of `[a] = [b]`. -/
theorem eqMask_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {a b : Nat} (ha : a < 16) (hb : b < 16) :
    WP isa (seqs (eqMask a b)) s fun t => KS I s₀ t ∧ t.mem = s.mem ∧
      t.gpr .x15 = mask (decide (av I s.mem a = av I s.mem b)) ∧ t.gpr .x7 = 0 ∧
      Keep [.x3, .x4, .x7, .x9, .x11, .x12, .x14, .x15, .x16, .x17] s t := by
  unfold eqMask
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok h.ws ha hb) fun s₁ ⟨hz, m₁, _, _, k₁⟩ => ?_)
  simp only [seqs]
  refine WP.mono (zeroMask_ok s₁) fun t ⟨⟨h15, h7, m₂⟩, k₂⟩ => ?_
  rw [decide_eq_decide.mpr hz] at h15
  have kk := k₁.trans k₂
  exact ⟨h.regs (by rw [m₂, m₁]) kk, by rw [m₂, m₁], h15, h7, kk.mono (by decide)⟩

/-- `neMask a b`: `x15 := ` the mask of `[a] ≠ [b]`. -/
theorem neMask_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {a b : Nat} (ha : a < 16) (hb : b < 16) :
    WP isa (seqs (neMask a b)) s fun t => KS I s₀ t ∧ t.mem = s.mem ∧
      t.gpr .x15 = mask (!decide (av I s.mem a = av I s.mem b)) ∧ t.gpr .x7 = 0 ∧
      Keep [.x3, .x4, .x7, .x9, .x11, .x12, .x14, .x15, .x16, .x17] s t := by
  unfold neMask
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok h.ws ha hb) fun s₁ ⟨hz, m₁, _, _, k₁⟩ => ?_)
  simp only [seqs]
  refine WP.mono (nonzeroMask_ok s₁) fun t ⟨⟨h15, h7, m₂⟩, k₂⟩ => ?_
  rw [decide_eq_decide.mpr hz] at h15
  have kk := k₁.trans k₂
  exact ⟨h.regs (by rw [m₂, m₁]) kk, by rw [m₂, m₁], h15, h7, kk.mono (by decide)⟩

/-- `ws` and `x14 := W`. -/
theorem wsMov_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block (ws ++ ([mov .x14 .x12] : List Instr))) s fun t =>
      (t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧
        t.gpr .x14 = BitVec.ofNat 64 w ∧ t.mem = s.mem ∧ t.c = s.c) ∧ Keep [.x11, .x12, .x14] s t := by
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, c₁⟩, k₁⟩ => ?_
  refine WP.mono (WP.keep [.x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.mem = s₁.mem ∧ t.c = s₁.c)
    (by brun [h12]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h14, m₂, c₂⟩, k₂⟩ => ?_
  exact ⟨⟨(k₂.gpr .x12 (by decide)).trans h12, (k₂.gpr .x11 (by decide)).trans h11, h14, m₂.trans m₁,
    c₂.trans c₁⟩, (k₁.trans k₂).mono (by decide)⟩

/-- `selC j`: `[j] := x15 ? [aC] : [j]`. -/
theorem selC_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {j : Nat} (hj : j < 16) (hjC : j ≠ aC)
    {c : Bool} (h15 : s.gpr .x15 = mask c) :
    WP isa (seqs (selC j)) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr j] s.mem t.mem ∧
      av I t.mem j = (if c then av I s.mem aC else av I s.mem j) ∧ atop I t.mem j = atop I s.mem j ∧
      Keep [.x3, .x4, .x11, .x12, .x14, .x16, .x17] s t := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  have sC := h.ws.sl (j := aC) (by decide)
  have sp := slot_sep (w := I.W) hjC
  simp only [selC, seqs]
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (wsMov_ok h.ws) fun s₁ ⟨⟨h12, h11, h14, m₁, _⟩, k₁⟩ =>
    WP.mono (base2_ok aC j .x16 .x17 ((k₁.gpr .x0 (by decide)).trans h.ws.x0) h11)
      fun s₂ ⟨⟨h16, h17, m₂, _⟩, k₂⟩ => ?_))
  have k12 := k₁.trans k₂
  refine WP.mono (selLoop_ok (h.ws.scr.congr k12.wr) h16 h17 ((k₂.gpr .x14 (by decide)).trans h14)
    ((k12.gpr .x15 (by decide)).trans h15) (by have := h.ws.w1; omega) (by have := h.ws.w2; omega)
    (by omega) (by omega) (by omega)) fun t ⟨hv, o, k₃⟩ => ?_
  rw [m₂, m₁] at hv o
  have f := KF.arr1 (B := I.B) (W := I.W) (j := j) o (Nat.le_refl _) (by omega)
  have kk := k12.trans k₃
  exact ⟨h.step f (all_mut_arr hj) kk, f, hv, o.word (Or.inr (Nat.le_refl _)) (by omega), kk.mono (by decide)⟩

/-- `(x & 1) − 1`: the mask of `x` even. -/
theorem mask_even (x : BitVec 64) :
    (x &&& BitVec.setWidth 64 1#16) - BitVec.ofNat 64 1 = mask (decide (x.toNat % 2 = 0)) := by
  have h2 : x &&& BitVec.setWidth 64 1#16 = BitVec.ofNat 64 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (BitVec.setWidth 64 1#16).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
    omega
  rw [h2]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

/-- The low bit of a word's array is the low bit of its value. -/
theorem word_mod2 {I : KIn} {m : Mem} {j : Nat} (hw : 1 ≤ I.W) :
    (word m I.B (slot I.W j)).toNat % 2 = av I m j % 2 := by
  rw [← wv_mod64 m I.B (slot I.W j) (n := I.W) hw, Nat.mod_mod_of_dvd _ (by decide)]

/-- `ws` and the base of array `j` into `x16`. -/
theorem wsBase16_ok {I : KIn} {s₀ s : State} (h : KS I s₀ s) (j : Nat) :
    WP isa (.block (ws ++ base j .x16)) s fun t =>
      (t.gpr .x16 = off I.B (slot I.W j) ∧ t.gpr .x12 = BitVec.ofNat 64 I.W ∧
        t.gpr .x11 = BitVec.ofNat 64 (8 * (I.W + 2)) ∧ t.mem = s.mem) ∧ Keep [.x11, .x12, .x16] s t := by
  rw [WP.block_append_iff]
  refine WP.mono h.ws.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok j .x16 ((k₁.gpr .x0 (by decide)).trans h.ws.x0) h11) fun t ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  exact ⟨⟨h16, (k₂.gpr .x12 (by decide)).trans h12, (k₂.gpr .x11 (by decide)).trans h11, m₂.trans m₁⟩,
    (k₁.trans k₂).mono (by decide)⟩

/-- `oddMaskOf j`: `x15 := ` the mask of `[j]` odd. -/
theorem oddMaskOf_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {j : Nat} (hj : j < 16) :
    WP isa (.block (oddMaskOf j)) s fun t => KS I s₀ t ∧ t.mem = s.mem ∧
      t.gpr .x15 = mask (decide (av I s.mem j % 2 = 1)) ∧ t.gpr .x7 = 0 ∧ t.gpr .x12 = BitVec.ofNat 64 I.W ∧
      t.gpr .x11 = BitVec.ofNat 64 (8 * (I.W + 2)) ∧ Keep [.x3, .x4, .x7, .x11, .x12, .x15, .x16] s t := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  unfold oddMaskOf
  rw [List.append_assoc, List.append_assoc, ← List.append_assoc ws, WP.block_append_iff]
  refine WP.mono (wsBase16_ok h j) fun s₁ ⟨⟨h16, h12, h11, m₁⟩, k₁⟩ => ?_
  have hs₁ := h.ws.scr.congr k₁.wr
  refine WP.mono (WP.keep [.x3, .x4, .x7, .x15] (Q := fun t => t.mem = s.mem ∧ t.gpr .x7 = 0 ∧
      t.gpr .x15 = mask (decide (av I s.mem j % 2 = 1))) (by
    brun [oddMask, h16, hs₁.ld (d := slot I.W j) (by omega), m₁, mask_low', word_mod2 (j := j) hw1])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨m₂, h7, h15⟩, k₂⟩ => ?_
  have kk := k₁.trans k₂
  exact ⟨h.regs m₂ kk, m₂, h15, h7, (k₂.gpr .x12 (by decide)).trans h12, (k₂.gpr .x11 (by decide)).trans h11,
    kk.mono (by decide)⟩

/-- `evenMaskOf j`: `x15 := ` the mask of `[j]` even. -/
theorem evenMaskOf_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {j : Nat} (hj : j < 16) :
    WP isa (.block (evenMaskOf j)) s fun t => KS I s₀ t ∧ t.mem = s.mem ∧
      t.gpr .x15 = mask (decide (av I s.mem j % 2 = 0)) ∧ t.gpr .x12 = BitVec.ofNat 64 I.W ∧
      t.gpr .x11 = BitVec.ofNat 64 (8 * (I.W + 2)) ∧ Keep [.x3, .x4, .x11, .x12, .x15, .x16] s t := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  unfold evenMaskOf
  rw [WP.block_append_iff]
  refine WP.mono (wsBase16_ok h j) fun s₁ ⟨⟨h16, h12, h11, m₁⟩, k₁⟩ => ?_
  have hs₁ := h.ws.scr.congr k₁.wr
  refine WP.mono (WP.keep [.x3, .x4, .x15] (Q := fun t => t.mem = s.mem ∧
      t.gpr .x15 = mask (decide (av I s.mem j % 2 = 0))) (by
    brun [h16, hs₁.ld (d := slot I.W j) (by omega), m₁, mask_even, word_mod2 (j := j) hw1])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨m₂, h15⟩, k₂⟩ => ?_
  have kk := k₁.trans k₂
  exact ⟨h.regs m₂ kk, m₂, h15, (k₂.gpr .x12 (by decide)).trans h12, (k₂.gpr .x11 (by decide)).trans h11,
    kk.mono (by decide)⟩

/-- `setOneA j` on a zero array: `[j] := 1` over `W + 2` words. -/
theorem setOne_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {j : Nat} (hj : j < 16)
    (hz : wv s.mem I.B (slot I.W j) (I.W + 2) = 0) :
    WP isa (.block (setOneA j)) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr j] s.mem t.mem ∧
      wv t.mem I.B (slot I.W j) (I.W + 2) = 1 ∧ Keep [.x11, .x12, .x16, .x3] s t := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  refine WP.mono (setOneA_ok h.ws hj) fun t ⟨hm, k⟩ => ?_
  have o := writeW_outside s.mem I.B (1 : BitVec 64) (d := slot I.W j) (by omega)
  rw [← hm] at o
  have f := KF.arr1 (B := I.B) (W := I.W) (j := j) o (Nat.le_refl _) (by omega)
  exact ⟨h.step f (all_mut_arr hj) k, f, by rw [hm, wv_put0 _ hz (by omega)]; rfl, k⟩

/-! ## Division and inverses -/

/-- `divmod q r d t`: `[r] := [q] mod [d]`, `[q] := [q] / [d]`. -/
theorem divmod_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {iQ iR iD iT : Nat}
    (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16) (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT)
    (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT) :
    WP isa (divmod iQ iR iD iT) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr iQ, .arr iR, .arr iT] s.mem t.mem ∧
      (0 < av I s.mem iD →
        wv t.mem I.B (slot I.W iR) (I.W + 1) = av I s.mem iQ % av I s.mem iD ∧
        av I t.mem iQ = av I s.mem iQ / av I s.mem iD) := by
  refine WP.mono (divmod_ok h.ws hQ hR hD hT dQR dQD dQT dRD dRT dDT) fun t ⟨_, hf, k, hv⟩ => ?_
  have f : KF I.B I.W [.arr iQ, .arr iR, .arr iT] s.mem t.mem := hf
  exact ⟨h.step f (all_mut_arrs (js := [iQ, iR, iT]) (by simp [hQ, hR, hT])) k, f, hv⟩

/-- The divisor's remainder, over `W` words. -/
theorem divmod_rem {I : KIn} {m : Mem} {iR : Nat} {a d : Nat} (ha : a < 2 ^ (64 * I.W))
    (h : wv m I.B (slot I.W iR) (I.W + 1) = a % d) : av I m iR = a % d :=
  (wv_low_of_lt (Nat.le_succ _) (by rw [h]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha)).trans h

/-- `inverse u v x₁ x₂ m t` from `v = m`, `x₁ = 1`, `x₂ = 0` and word `W`
of `u` zero: for an odd `m > 1`, `v = gcd(u, m)` and `x₂ u ≡ v (mod m)`,
`x₂ < m`. -/
theorem inverse_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {iU iV iX₁ iX₂ iM iT : Nat}
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT) (hU0 : atop I s.mem iU = 0)
    (hVM : av I s.mem iV = av I s.mem iM) (hX1 : av I s.mem iX₁ = 1) (hX2 : av I s.mem iX₂ = 0) :
    WP isa (inverse iU iV iX₁ iX₂ iM iT) s fun t => KS I s₀ t ∧
      KF I.B I.W [.arr iU, .arr iV, .arr iX₁, .arr iX₂, .arr iT] s.mem t.mem ∧
      (av I s.mem iM % 2 = 1 → 1 < av I s.mem iM →
        av I t.mem iV = Nat.gcd (av I s.mem iU) (av I s.mem iM) ∧
        ((av I s.mem iM : Nat) : Int) ∣ (av I t.mem iX₂ : Int) * av I s.mem iU - av I t.mem iV ∧
        av I t.mem iX₂ < av I s.mem iM) := by
  refine WP.mono (inverse_ok h.ws hU hV hX₁ hX₂ hM hT dUV dUX₁ dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T dX₂M
    dX₂T dMT hU0 hVM hX1 hX2) fun t ⟨_, hf, k, hv⟩ => ?_
  have f : KF I.B I.W [.arr iU, .arr iV, .arr iX₁, .arr iX₂, .arr iT] s.mem t.mem :=
    KF.of_frm hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨.arr iU, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
      · exact ⟨.arr iV, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
      · exact ⟨.arr iX₁, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
      · exact ⟨.arr iX₂, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
      · exact ⟨.arr iT, by simp, by simp [Rc.range], by simp [Rc.range]⟩
  exact ⟨h.step f (all_mut_arrs (js := [iU, iV, iX₁, iX₂, iT]) (by simp [hU, hV, hX₁, hX₂, hT])) k, f, hv⟩

end VG.Proof.RsaKeyGen.AArch64.Key
