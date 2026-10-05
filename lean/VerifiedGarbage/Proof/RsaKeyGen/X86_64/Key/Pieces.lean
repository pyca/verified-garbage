import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.State
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Bignum.X86_64.Cmp

/-!
# An RSA key from its primes on x86-64: the pieces

The routines the code is made of, from `KS`: what each leaves in the arrays
(`av`, the low `W` words of one), and the parts it changes (`KF`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- Array `j`'s value: its low `W` words. -/
abbrev av (I : KIn) (m : Mem) (j : Nat) : Nat := wv m I.B (slot I.W j) I.W

/-- Word `W` of array `j`. -/
abbrev atop (I : KIn) (m : Mem) (j : Nat) : BitVec 64 := word m I.B (slot I.W j + 8 * I.W)

/-- `KF.arr` for `av`. -/
theorem KF.av {I : KIn} {cs : List Rc} {m m' : Mem} (h : KF I.B I.W cs m m') (hok : cs.all Rc.ok = true)
    {j : Nat} (hj : j < 16) (hn : .arr j ∉ cs) (hZ : slot I.W 16 ≤ 2 ^ 64) : av I m' j = av I m j :=
  h.arr hok hj hn hZ

/-- `KF.top` for `atop`. -/
theorem KF.at {I : KIn} {cs : List Rc} {m m' : Mem} (h : KF I.B I.W cs m m') (hok : cs.all Rc.ok = true)
    {j : Nat} (hj : j < 16) (hn : .arr j ∉ cs) (hZ : slot I.W 16 ≤ 2 ^ 64) : atop I m' j = atop I m j :=
  h.top hok hj hn hZ

theorem all_mut_arr {j : Nat} (hj : j < 16) : [Rc.arr j].all Rc.mut = true := by
  simp only [List.all_cons, List.all_nil, Rc.mut, Bool.and_true, decide_eq_true_eq]; exact hj

theorem KF.arr1 {I : KIn} {m m' : Mem} {j : Nat} {o n : Nat} (h : Outside I.B o n m m') (h1 : slot I.W j ≤ o)
    (h2 : o + n ≤ slot I.W j + 8 * (I.W + 2)) : KF I.B I.W [.arr j] m m' :=
  KF.of_outside h (.arr j) (List.mem_singleton_self _) h1 h2

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

/-! ## Clearing and copying -/

theorem zeroA_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16) :
    WP isa (zeroA j) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr j] s.mem t.mem ∧
      wv t.mem I.B (slot I.W j) (I.W + 2) = 0 ∧ Keep [.r12, .r9, .r8, .rax, .r14] s t :=
  WP.mono (zeroA_ok h.ws hj) fun t ⟨hz, o, k⟩ =>
    have f := KF.arr1 o (Nat.le_refl _) (Nat.le_refl _)
    ⟨h.step f (all_mut_arr hj) k (by decide), f, hz, k⟩

theorem copyA_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {o a : Nat} (ho : o < 16) (ha : a < 16)
    (hoa : o ≠ a) :
    WP isa (copyA o a) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr o] s.mem t.mem ∧
      av I t.mem o = av I s.mem a ∧ atop I t.mem o = atop I s.mem o ∧
      Keep [.r12, .r9, .rsi, .rbx, .rax, .r14] s t :=
  WP.mono (copyA_ok h.ws ho ha hoa) fun t ⟨hv, o', k⟩ =>
    have f := KF.arr1 o' (Nat.le_refl _) (by omega)
    have hn := h.ws.scr.nowrap
    have := h.ws.sl ho
    ⟨h.step f (all_mut_arr ho) k (by decide), f, hv, o'.word (Or.inr (Nat.le_refl _)) (by omega), k⟩

/-- `zeroA` then `copyA`: `[o] := [a]` with words `W` and `W + 1` zero. -/
theorem zc_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {o a : Nat} (ho : o < 16) (ha : a < 16)
    (hoa : o ≠ a) :
    WP isa (seqs [zeroA o, copyA o a]) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr o] s.mem t.mem ∧
      av I t.mem o = av I s.mem a ∧ atop I t.mem o = 0 := by
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h ho) fun s₁ ⟨h₁, f₁, z₁, _⟩ => ?_)
  refine WP.mono (copyA_k h₁ ho ha hoa) fun t ⟨ht, f₂, v₂, t₂, _⟩ => ⟨ht, ?_, ?_, ?_⟩
  · exact (f₁.trans f₂).mono (by simp)
  · rw [v₂]; exact f₁.arr (by simp [Rc.ok, ho]) ha (by simp [hoa.symm]) h.hZ
  · rw [t₂]; exact (wv_zero2 z₁).2

/-- `constA x`: `[aC] := x` over `W + 2` words. -/
theorem constA_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (x : BitVec 32) :
    WP isa (seqs (constA x)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aC] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aC) (I.W + 2) = x.toNat ∧ Keep [.r12, .r9, .r8, .rax, .r14, .rbx] s t := by
  have hn := h.ws.scr.nowrap
  have sC := h.ws.sl (j := aC) (by decide)
  simp only [constA, seqs]
  refine WP.seq (WP.mono (zeroA_k h (j := aC) (by decide)) fun s₁ ⟨h₁, f₁, z₁, k₁⟩ => ?_)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h₁.ws.ws_ok fun s₂ ⟨_, h9, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aC (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h₁.ws.rdi) h9)
    fun s₃ ⟨hbx, m₃, k₃⟩ => ?_
  have hs₃ := h₁.ws.scr.congr (k₂.trans k₃).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s₁.mem.writeW (off I.B (slot I.W aC)) (x.setWidth 64)) (by
    xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₃.st (d := slot I.W aC) (by omega), m₃, m₂]) rfl) fun t ⟨hm, k₄⟩ => ?_
  have o₄ := writeW_outside s₁.mem I.B (x.setWidth 64) (d := slot I.W aC) (by omega)
  rw [← hm] at o₄
  have f₄ := KF.arr1 (j := aC) o₄ (Nat.le_refl _) (by omega)
  have kk := (k₂.trans k₃).trans k₄
  refine ⟨h₁.step f₄ (all_mut_arr (by decide)) kk (by decide), (f₁.trans f₄).mono (by simp), ?_,
    (k₁.trans kk).mono (by simp)⟩
  rw [hm]
  have := wv_put (m := s₁.mem) (B := I.B) (d := slot I.W aC) (N := I.W + 2) (k := 0) (x.setWidth 64)
    ((wv_eq_zero_iff _ _ _ _).mp z₁) (by omega) (by omega) (I.W + 2) (Nat.le_refl _)
  rw [Nat.mul_zero, Nat.add_zero] at this
  rw [this]
  rw [ite_eq_left (show 0 < I.W + 2 by omega), Nat.pow_zero, Nat.one_mul, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))

/-- A number of `W + 2` words below `2^(64 W)` is its low `W` words. -/
theorem av_of_full {I : KIn} {m : Mem} {j v : Nat} (h : wv m I.B (slot I.W j) (I.W + 2) = v)
    (hv : v < 2 ^ (64 * I.W)) : av I m j = v :=
  (wv_low_of_lt (Nat.le_add_right _ 2) (by rw [h]; exact hv)).trans h

/-! ## Masks -/

/-- `ltA a b`: `rbp := ` the mask of `[a] < [b]`. -/
theorem ltA_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {a b : Nat} (ha : a < 16) (hb : b < 16) :
    WP isa (seqs (ltA a b)) s fun t => KS I m₀ t ∧ t.mem = s.mem ∧
      t.gpr .rbp = mask (decide (av I s.mem a < av I s.mem b)) ∧
      t.gpr .rbx = off I.B (slot I.W a) ∧ t.gpr .r10 = off I.B (slot I.W b) ∧ t.gpr .r12 = BitVec.ofNat 64 I.W ∧
      Keep [.r12, .r9, .rbx, .r10, .rbp, .rax, .r14] s t := by
  have hn := h.ws.scr.nowrap
  have sa := h.ws.sl ha
  have sb := h.ws.sl hb
  simp only [ltA, seqs]
  have hb : WP isa (.block (ws ++ base a .rbx ++ base b .r10 ++ [.mov32 .rbp (.imm 0)])) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 I.W ∧ t.gpr .rbx = off I.B (slot I.W a) ∧
      t.gpr .r10 = off I.B (slot I.W b) ∧ t.gpr .rbp = mask false ∧ t.mem = s.mem ∧
      Keep [.r12, .r9, .rbx, .r10, .rbp] s t := by
    rw [List.append_assoc, List.append_assoc]
    refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_)
    refine WP.mono (base_ok a (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.ws.rdi) h9)
      fun s₂ ⟨hbx, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok b (r := .r10) (by decide) (((k₁.trans k₂).gpr (by decide)).trans h.ws.rdi)
      ((k₂.gpr (by decide)).trans h9)) fun s₃ ⟨h10, m₃, k₃⟩ => ?_
    refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask false ∧ t.mem = s₃.mem) (by xrun) rfl)
      fun t ⟨⟨hbp, hm⟩, k₄⟩ => ⟨((k₂.trans k₃).trans k₄).gpr (by decide) |>.trans h12,
        (k₃.trans k₄).gpr (by decide) |>.trans hbx, (k₄.gpr (by decide)).trans h10, hbp,
        by rw [hm, m₃, m₂, m₁], (((k₁.trans k₂).trans k₃).trans k₄).mono (by simp)⟩
  refine WP.seq (WP.mono hb ?_)
  · intro s₁ ⟨h12, hbx, h10, hbp, m₁, k₁⟩
    refine WP.mono (cmpLoop_ok (h.ws.scr.congr k₁.2.2) hbx h10 h12 hbp (by have := h.ws.w1; omega)
      (by have := h.ws.w2; omega) (by omega) (by omega)) fun t ⟨hbp', m₂, k₂⟩ => ?_
    rw [m₁] at hbp'
    have kk := k₁.trans k₂
    exact ⟨h.step (cs := []) (by rw [m₂, m₁]; exact KF.refl _ _ _) rfl kk (by decide), by rw [m₂, m₁], hbp',
      (k₂.gpr (by decide)).trans hbx, (k₂.gpr (by decide)).trans h10, (k₂.gpr (by decide)).trans h12,
      kk.mono (by simp)⟩

theorem isZero_mask {x : BitVec 64} {c : Prop} [Decidable c] (hx : x = 0 ↔ c) :
    0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (x.toNat < BitVec.toNat (1 : BitVec 64)))) = mask (decide c) := by
  by_cases hc : c
  · rw [hx.mpr hc, decide_eq_true hc]; decide
  · have : x ≠ 0 := fun e => hc (hx.mp e)
    have : ¬ x.toNat < 1 := fun h => this (BitVec.eq_of_toNat_eq (by simp; omega))
    rw [decide_eq_false hc]
    simp [this, mask]

/-- `eqMask a b`: `rbp := ` the mask of `[a] = [b]`. -/
theorem eqMask_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {a b : Nat} (ha : a < 16) (hb : b < 16) :
    WP isa (seqs (eqMask a b)) s fun t => KS I m₀ t ∧ t.mem = s.mem ∧
      t.gpr .rbp = mask (decide (av I s.mem a = av I s.mem b)) ∧
      Keep [.r12, .r9, .rbx, .r10, .rbp, .rax, .r14] s t := by
  rw [eqMask]
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok h.ws ha hb) fun s₁ ⟨hz, m₁, k₁⟩ => ?_)
  simp only [seqs]
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask (decide (av I s.mem a = av I s.mem b)) ∧
    t.mem = s₁.mem) ?_ rfl) fun t ⟨⟨hbp, m₂⟩, k₂⟩ => ?_
  · unfold isZero
    xrun
    exact isZero_mask hz
  · have kk := k₁.trans k₂
    exact ⟨h.step (cs := []) (by rw [m₂, m₁]; exact KF.refl _ _ _) rfl kk (by decide), by rw [m₂, m₁], hbp,
      kk.mono (by simp)⟩

/-- `selC j`: `[j] := rbp ? [j] : [aC]`. -/
theorem selC_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16) (hjC : j ≠ aC)
    {c : Bool} (hbp : s.gpr .rbp = mask c) :
    WP isa (seqs (selC j)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr j] s.mem t.mem ∧
      av I t.mem j = (if c then av I s.mem j else av I s.mem aC) ∧ atop I t.mem j = atop I s.mem j ∧
      Keep [.r12, .r9, .r8, .rsi, .rax, .rdx, .r14] s t := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  have sC := h.ws.sl (j := aC) (by decide)
  have sp := slot_far (w := I.W) hjC
  simp only [selC, seqs]
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base2_ok j aC (r₁ := .r8) (r₂ := .rsi) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans h.ws.rdi) h9 (by decide)) fun s₂ ⟨h8, hsi, m₂, k₂⟩ => ?_))
  refine WP.mono (sel_ok (h.ws.scr.congr (k₁.trans k₂).2.2) h8 hsi (((k₁.trans k₂).gpr (by decide)).trans hbp)
    ((k₂.gpr (by decide)).trans h12) (by have := h.ws.w1; omega) (by have := h.ws.w2; omega) (by omega) (by omega)
    (by omega)) fun t ⟨hv, o, k₃⟩ => ?_
  rw [m₂, m₁] at hv o
  have f := KF.arr1 (I := I) (j := j) o (Nat.le_refl _) (by omega)
  have kk := (k₁.trans k₂).trans k₃
  exact ⟨h.step f (all_mut_arr hj) kk (by decide), f, hv, o.word (Or.inr (Nat.le_refl _)) (by omega),
    kk.mono (by simp)⟩

/-- `subC o a`: `[o] := [a] - ([aC] & r15)` over `W` words. -/
theorem subC_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {o a : Nat} (ho : o < 16) (ha : a < 16)
    (hoC : o ≠ aC) (haC : a ≠ aC) (hoa : o = a ∨ o ≠ a) {c : Bool} (h15 : s.gpr .r15 = mask c) :
    WP isa (seqs (subC o a)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr o] s.mem t.mem ∧
      (∃ b : Bool, av I t.mem o + (if c then av I s.mem aC else 0) = av I s.mem a + 2 ^ (64 * I.W) * b.toNat) ∧
      atop I t.mem o = atop I s.mem o ∧ Keep [.r12, .r9, .r8, .r10, .rsi, .rbp, .rax, .rdx, .r14] s t := by
  have hn := h.ws.scr.nowrap
  have so := h.ws.sl ho
  have sa := h.ws.sl ha
  have sC := h.ws.sl (j := aC) (by decide)
  have pC := slot_far (w := I.W) hoC
  have pA : slot I.W o ≤ slot I.W a ∨ slot I.W a + 8 * I.W ≤ slot I.W o := by
    rcases hoa with rfl | hne
    · exact Or.inl (Nat.le_refl _)
    · have := slot_far (w := I.W) hne; omega
  simp only [subC, seqs]
  have hb : WP isa (.block (ws ++ base a .r8 ++ base aC .r10 ++ base o .rsi ++ [.mov32 .rbp (.imm 0)])) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 I.W ∧ t.gpr .r8 = off I.B (slot I.W a) ∧ t.gpr .r10 = off I.B (slot I.W aC) ∧
      t.gpr .rsi = off I.B (slot I.W o) ∧ t.gpr .rbp = mask false ∧ t.mem = s.mem ∧
      Keep [.r12, .r9, .r8, .r10, .rsi, .rbp] s t := by
    simp only [List.append_assoc]
    refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_)
    have hdi₁ : s₁.gpr .rdi = I.B := (k₁.gpr (by decide)).trans h.ws.rdi
    refine WP.mono (base_ok a (r := .r8) (by decide) hdi₁ h9) fun s₂ ⟨h8, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok aC (r := .r10) (by decide) ((k₂.gpr (by decide)).trans hdi₁)
      ((k₂.gpr (by decide)).trans h9)) fun s₃ ⟨h10, m₃, k₃⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok o (r := .rsi) (by decide) (((k₂.trans k₃).gpr (by decide)).trans hdi₁)
      (((k₂.trans k₃).gpr (by decide)).trans h9)) fun s₄ ⟨hsi, m₄, k₄⟩ => ?_
    refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask false ∧ t.mem = s₄.mem) (by xrun) rfl)
      fun t ⟨⟨hbp, hm⟩, k₅⟩ => ⟨(((k₂.trans k₃).trans k₄).trans k₅).gpr (by decide) |>.trans h12,
        ((k₃.trans k₄).trans k₅).gpr (by decide) |>.trans h8, ((k₄.trans k₅).gpr (by decide)).trans h10,
        (k₅.gpr (by decide)).trans hsi, hbp, by rw [hm, m₄, m₃, m₂, m₁],
        ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by simp)⟩
  refine WP.seq (WP.mono hb fun s₁ ⟨h12, h8, h10, hsi, hbp, m₁, k₁⟩ => ?_)
  refine WP.mono (subM_ok (h.ws.scr.congr k₁.2.2) hsi h8 h10 ((k₁.gpr (by decide)).trans h15) h12 hbp
    (by have := h.ws.w1; omega) (by have := h.ws.w2; omega) (by omega) (by omega) (by omega) pA (by omega))
    fun t ⟨b, _, hv, o', k₂⟩ => ?_
  rw [m₁] at hv o'
  have f := KF.arr1 (I := I) (j := o) o' (Nat.le_refl _) (by omega)
  have kk := k₁.trans k₂
  exact ⟨h.step f (all_mut_arr ho) kk (by decide), f, ⟨b, hv⟩, o'.word (Or.inr (Nat.le_refl _)) (by omega),
    kk.mono (by simp)⟩

/-- `oddMask j`: `rax := ` the mask of `[j]` odd. -/
theorem oddMask_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16) :
    WP isa (.block (oddMask j)) s fun t => t.mem = s.mem ∧ t.gpr .rax = mask (decide (av I s.mem j % 2 = 1)) ∧
      t.gpr .r12 = BitVec.ofNat 64 I.W ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (I.W + 2)) ∧
      Keep [.r12, .r9, .rbx, .rax, .rdx] s t := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  unfold oddMask
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok j (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.ws.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  have hs₂ := h.ws.scr.congr (k₁.trans k₂).2.2
  have e0 : (s₂.mem.readW (off I.B (slot I.W j)) 64).toNat % 2 = av I s.mem j % 2 := by
    rw [m₂, m₁, ← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide)]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = s₂.mem ∧
    t.gpr .rax = mask (decide (av I s.mem j % 2 = 1))) (by
      xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        hs₂.ld (d := slot I.W j) (by omega), mask_low, e0]) rfl) fun t ⟨⟨hm, hax⟩, k₃⟩ =>
    ⟨by rw [hm, m₂, m₁], hax, ((k₂.trans k₃).gpr (by decide)).trans h12, ((k₂.trans k₃).gpr (by decide)).trans h9,
      ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `setOneA j` on a zero array: `[j] := 1` over `W + 2` words. -/
theorem setOne_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16)
    (hz : wv s.mem I.B (slot I.W j) (I.W + 2) = 0) :
    WP isa (.block (setOneA j)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr j] s.mem t.mem ∧
      wv t.mem I.B (slot I.W j) (I.W + 2) = 1 ∧ Keep [.r12, .r9, .rbx, .rax] s t := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  refine WP.mono (setOneA_ok h.ws hj) fun t ⟨hm, k⟩ => ?_
  have o := writeW_outside s.mem I.B (1 : BitVec 64) (d := slot I.W j) (by omega)
  rw [← hm] at o
  have f := KF.arr1 (I := I) (j := j) o (Nat.le_refl _) (by omega)
  refine ⟨h.step f (all_mut_arr hj) k (by decide), f, ?_, k⟩
  rw [hm]
  have := wv_put (m := s.mem) (B := I.B) (d := slot I.W j) (N := I.W + 2) (k := 0) (1 : BitVec 64)
    ((wv_eq_zero_iff _ _ _ _).mp hz) (by omega) (by omega) (I.W + 2) (Nat.le_refl _)
  rw [Nat.mul_zero, Nat.add_zero] at this
  rw [this, ite_eq_left (show 0 < I.W + 2 by omega)]
  rfl

/-! ## Division and inverses -/

theorem all_mut_arrs {js : List Nat} (h : ∀ j ∈ js, j < 16) : (js.map Rc.arr).all Rc.mut = true :=
  List.all_eq_true.mpr fun c hc => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    simp only [Rc.mut, decide_eq_true_eq]; exact h j hj

/-- `divmod q r d t`: `[r] := [q] mod [d]`, `[q] := [q] / [d]`. -/
theorem divmod_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {iQ iR iD iT : Nat}
    (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16) (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT)
    (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT) :
    WP isa (divmod iQ iR iD iT) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr iQ, .arr iR, .arr iT] s.mem t.mem ∧
      (0 < av I s.mem iD →
        wv t.mem I.B (slot I.W iR) (I.W + 1) = av I s.mem iQ % av I s.mem iD ∧
        av I t.mem iQ = av I s.mem iQ / av I s.mem iD) := by
  refine WP.mono (divmod_ok h.ws.scr h.ws.rdi h.ws.hw h.ws.hS (by have := h.ws.w1; omega) h.ws.w2 h.ws.hZ hQ hR hD hT
    dQR dQD dQT dRD dRT dDT) fun t ⟨hdi, hf, k, hv⟩ => ?_
  have f : KF I.B I.W [.arr iQ, .arr iR, .arr iT] s.mem t.mem := hf
  have k' : Keep (List.filter (· != .rdi) (.r9 :: .r11 :: stepRegs)) s t :=
    ⟨fun r hr => if e : r = .rdi then by rw [e, hdi, h.ws.rdi] else k.1 r fun hm => hr (List.mem_filter.mpr
      ⟨hm, by simp [e]⟩), k.2⟩
  exact ⟨h.step f (all_mut_arrs (js := [iQ, iR, iT]) (by simp [hQ, hR, hT])) k' (by decide), f, hv⟩

/-- `inverse u v x₁ x₂ m t` from `v = m`, `x₁ = 1`, `x₂ = 0` and word `W`
of `u` zero: for an odd `m > 1`, `v = gcd(u, m)` and `x₂ u ≡ v (mod m)`,
`x₂ < m`. -/
theorem inverse_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {iU iV iX₁ iX₂ iM iT : Nat}
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT) (hU0 : atop I s.mem iU = 0)
    (hVM : av I s.mem iV = av I s.mem iM) (hX1 : av I s.mem iX₁ = 1) (hX2 : av I s.mem iX₂ = 0) :
    WP isa (inverse iU iV iX₁ iX₂ iM iT) s fun t => KS I m₀ t ∧
      KF I.B I.W [.arr iU, .arr iV, .arr iX₁, .arr iX₂, .arr iT, .hdr sMo] s.mem t.mem ∧
      (av I s.mem iM % 2 = 1 → 1 < av I s.mem iM →
        av I t.mem iV = Nat.gcd (av I s.mem iU) (av I s.mem iM) ∧
        ((av I s.mem iM : Nat) : Int) ∣ (av I t.mem iX₂ : Int) * av I s.mem iU - av I t.mem iV ∧
        av I t.mem iX₂ < av I s.mem iM) := by
  refine WP.mono (inverse_ok h.ws.scr h.ws.rdi h.ws.hw h.ws.hS (by have := h.ws.w1; omega) h.ws.w2 h.ws.hZ hU hV hX₁
    hX₂ hM hT dUV dUX₁ dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T dX₂M dX₂T dMT hU0 hVM hX1 hX2)
    fun t ⟨hdi, hf, k, hv⟩ => ?_
  have f : KF I.B I.W [.arr iU, .arr iV, .arr iX₁, .arr iX₂, .arr iT, .hdr sMo] s.mem t.mem :=
    KF.of_frm hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨.arr iU, by simp, by simp [Rc.range], by simp [Rc.range]⟩
      · exact ⟨.arr iV, by simp, by simp [Rc.range], by simp [Rc.range]⟩
      · exact ⟨.arr iX₁, by simp, by simp [Rc.range], by simp [Rc.range]⟩
      · exact ⟨.arr iX₂, by simp, by simp [Rc.range], by simp [Rc.range]⟩
      · exact ⟨.arr iT, by simp, by simp [Rc.range], by simp [Rc.range]⟩
      · exact ⟨.hdr sMo, by simp, by simp [Rc.range], by simp [Rc.range]⟩
  have k' : Keep (List.filter (· != .rdi) (.r9 :: .r11 :: stepRegs)) s t :=
    ⟨fun r hr => if e : r = .rdi then by rw [e, hdi, h.ws.rdi] else k.1 r fun hm => hr (List.mem_filter.mpr
      ⟨hm, by simp [e]⟩), k.2⟩
  refine ⟨h.step f ?_ k' (by decide), f, hv⟩
  simp only [List.all_cons, List.all_nil, Rc.mut, sMo, sFn, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

end VG.Proof.RsaKeyGen.X86_64.Key
