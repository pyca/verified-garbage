module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Mont.PPC64LE.Csub
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# ECDSA on PPC64LE: the masks of the checks, and the flag

The checks of `Impl/Ecdsa/PPC64LE.lean` as masks, all ones or zero:
`nonzero a` sets `r5` to all ones iff `[a] ≠ 0` (`nonzero_ok`: the words
or'ed, then the top bit of `-x | x`), `ltM m a` sets `r5` to all ones iff
`[a] < [m]` (`ltM_ok`: the carry out of `[a] - [m]`, a 32-bit digit at a
time), and `andFlag` ands `r5` into the flag word (`andFlag_ok`); so
`checkRange a` ands the mask of `0 < [a] < [MN]` into the flag
(`checkRange_ok`) and `checkNonzero a` the mask of `[a] ≠ 0`
(`checkNonzero_ok`). As on 32-bit ARM (`Proof/Ecdsa/Arm/Flags.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE

/-! ## Nonzero -/

/-- One `or` of `nonzero`. -/
def orStep (a j : Nat) : List Instr := [.load .d .r4 wb (a + 8 * (j + 1)), .logic .or .r5 .r5 .r4]

theorem nonzero_eq (c : Cfg) (a : Nat) : c.nonzero a = ([.load .d .r5 wb a] : List Instr) ++
    ((List.range (c.n - 1)).flatMap (orStep a) ++
    ([.li .r4 0, .sub .r4 .r4 .r5, .logic .or .r4 .r4 .r5, .lsr .d .r4 .r4 63, .li .r5 0, .sub .r5 .r5 .r4] :
      List Instr)) := rfl

theorem or_eq_zero (x y : BitVec 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := BitVec.or_eq_zero_iff

/-- The `or`s of `nonzero`. -/
theorem ors_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0) {a : Nat}
    (ha4 : a % 4 = 0) : ∀ k, a + 8 * (k + 1) ≤ size →
    WP isa (.block ((List.range k).flatMap (orStep a))) s fun s' =>
      (s'.gpr .r5 = 0 ↔ s.gpr .r5 = 0 ∧ ∀ j < k, word s.mem base (a + 8 * (j + 1)) = 0) ∧
      Kp [.r4, .r5] s s' ∧ s'.mem = s.mem
  | 0, _ => WP.block_nil ⟨⟨fun h => ⟨h, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩, fun h => h.1⟩,
      Kp.refl _ _, rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine wp_append (WP.mono (ors_ok hs h3 ha4 k (by omega)) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    simp only [orStep]
    refine wp_step (ld0_ok (k₁.ws hs) (k₁.at h3) (by decide) (by omega) (by omega)) ?_
    refine wp_step exec_logic (WP.block_nil ⟨?_, (k₁.trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide)), by simp only [write_mem]; exact m₁⟩)
    simp only [write_gpr, ite_true, reduceCtorEq, ite_false, or_eq_zero, e₁, m₁]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, fun j hj => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h2 j hj
        · exact h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun j hj => h2 j (by omega)⟩, h2 k (by omega)⟩

/-- The top bit of `-x | x` is whether `x ≠ 0`. -/
theorem negOr_shr (x : BitVec 64) : ((BitVec.ofNat 64 0 - x) ||| x) >>> 63 = if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · subst hx; decide
  · rw [ite_eq_right hx]
    apply BitVec.eq_of_toNat_eq
    have h0 : x.toNat ≠ 0 := fun e => hx (BitVec.eq_of_toNat_eq e)
    have hlt := ((BitVec.ofNat 64 0 - x) ||| x).isLt
    have h1 : (BitVec.ofNat 64 0 - x).toNat ≤ ((BitVec.ofNat 64 0 - x) ||| x).toNat := by
      rw [BitVec.toNat_or]; exact Nat.left_le_or
    have h2 : x.toNat ≤ ((BitVec.ofNat 64 0 - x) ||| x).toNat := by rw [BitVec.toNat_or]; exact Nat.right_le_or
    have h3 : (BitVec.ofNat 64 0 - x).toNat = 2 ^ 64 - x.toNat := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := x.isLt; omega
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    show _ = 1
    omega

theorem neg_bit64 (b : Bool) : BitVec.ofNat 64 0 - (if b then 1 else 0) = mask64 (b = true) := by
  cases b <;> decide

/-- `r5` is all ones iff `[a] ≠ 0`; `r4` changes too. -/
theorem nonzero_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {a : Nat} (ha4 : a % 4 = 0) (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) :
    WP isa (.block (c.nonzero a)) s fun s' =>
      s'.gpr .r5 = mask64 (wordsVal s.mem base a c.n ≠ 0) ∧ Kp [.r4, .r5] s s' ∧ s'.mem = s.mem := by
  rw [nonzero_eq, List.singleton_append]
  refine wp_step (ld0_ok hs h3 (by decide) ha4 (by omega)) ?_
  refine wp_append (WP.mono (ors_ok (hs.write _ _) (h3.write _) ha4 (c.n - 1) (by omega)) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  simp only [write_gpr, ite_true, write_mem] at e₂ m₂
  have hz : s₂.gpr .r5 = 0 ↔ wordsVal s.mem base a c.n = 0 := by
    rw [e₂, wordsVal_eq_zero_iff]
    constructor
    · rintro ⟨h0, h⟩ j hj
      rcases j with _ | j
      · simpa using h0
      · exact h j (by omega)
    · intro h
      exact ⟨by simpa using h 0 hn, fun j hj => h (j + 1) (by omega)⟩
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub ?_
  refine wp_step exec_logic ?_
  refine wp_step (exec_lsr_d (by decide)) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub (WP.block_nil ⟨?_, ?_, ?_⟩)
  · simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    rw [negOr_shr]
    by_cases h : s₂.gpr .r5 = 0
    · rw [ite_eq_left_iff.mpr (fun h' => absurd h h')]
      simp only [show wordsVal s.mem base a c.n = 0 from hz.mp h, ne_eq, not_true_eq_false, mask64, ite_false]
      decide
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
      simp only [show wordsVal s.mem base a c.n ≠ 0 from fun e => h (hz.mpr e), ne_eq, not_false_eq_true,
        mask64, ite_true]
      decide
  · exact (((Kp.write _ _ (by decide)).trans k₂).trans ((((((Kp.write _ _ (by decide)).trans
      (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))))
  · simp only [write_mem]; exact m₂

/-! ## Less than a modulus -/

/-- The carry of digit `j` of `[a] - [m]`, from the carry `r6`. -/
theorem ltDigit_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size)
    (h3 : At s base .r3 0) (h0 : s.gpr .r0 = M32) (hc : (s.gpr .r6).toNat < 2 ^ 32) {m a j : Nat}
    (ha : a + 4 * j + 4 ≤ size) (hm : m + 4 * j + 4 ≤ size) :
    WP isa (.block (Cfg.ltDigit m a j)) s fun u =>
      (u.gpr .r6).toNat = (w32 s.mem base (a + 4 * j) + (2 ^ 32 - 1 - w32 s.mem base (m + 4 * j)) +
        (s.gpr .r6).toNat) / 2 ^ 32 ∧ Kp [.r6, .r7, .r8] s u ∧ u.mem = s.mem := by
  have t0 := w32_lt s.mem base (a + 4 * j)
  have t1 := w32_lt s.mem base (m + 4 * j)
  simp only [Cfg.ltDigit]
  refine wp_step (lwz0_ok hs h3 (by decide) ha) ?_
  refine wp_step (lwz0_ok (hs.write _ _) (h3.write _) (by decide) hm) ?_
  refine wp_step exec_add ?_
  refine wp_step exec_sub ?_
  refine wp_step exec_add ?_
  refine wp_step (exec_lsr_d (by decide)) (WP.block_nil ⟨?_, ?_, rfl⟩)
  · simp only [write_gpr, write_mem, reduceCtorEq, ite_false, ite_true, h0]
    have e : (BitVec.ofNat 64 (w32 s.mem base (a + 4 * j)) + M32 - BitVec.ofNat 64 (w32 s.mem base (m + 4 * j)) +
        s.gpr .r6).toNat = w32 s.mem base (a + 4 * j) + (2 ^ 32 - 1 - w32 s.mem base (m + 4 * j)) +
          (s.gpr .r6).toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_add, toNat_ofNat_lt (by omega),
        toNat_ofNat_lt (by omega), show M32.toNat = 2 ^ 32 - 1 from rfl]
      omega
    rw [BitVec.toNat_ushiftRight, e, Nat.shiftRight_eq_div_pow]
  · exact ((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide)) |>.trans (Kp.write _ _ (by decide))

/-- The order of numbers of `k + 1` digits, from their top digits and the
order of the rest. -/
theorem lt_top {P M A x y : Nat} (hM : M < P) (hA : A < P) :
    M + P * x ≤ A + P * y ↔ x < y ∨ (x = y ∧ M ≤ A) := by
  rcases Nat.lt_trichotomy x y with h | rfl | h
  · have := Nat.mul_le_mul_left P (show x + 1 ≤ y from h)
    rw [Nat.mul_succ] at this
    omega
  · omega
  · have := Nat.mul_le_mul_left P (show y + 1 ≤ x from h)
    rw [Nat.mul_succ] at this
    omega

/-- The digits of `ltM`. -/
def ltDigits (m a k : Nat) : List Instr := (List.range k).flatMap (Cfg.ltDigit m a)

theorem ltDigits_succ (m a k : Nat) : ltDigits m a (k + 1) = ltDigits m a k ++ Cfg.ltDigit m a k := by
  simp only [ltDigits, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- After `k` digits, the carry is 1 iff the low `k` digits of `[m]` are at
most `[a]`'s. -/
theorem ltDigits_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size)
    (h3 : At s base .r3 0) (h0 : s.gpr .r0 = M32) (hc : s.gpr .r6 = BitVec.ofNat 64 1) {m a W : Nat}
    (ha : a + 4 * W ≤ size) (hm : m + 4 * W ≤ size) : ∀ {k : Nat}, k ≤ W →
    WP isa (.block (ltDigits m a k)) s fun u =>
      (u.gpr .r6).toNat = (if val32 s.mem base m k ≤ val32 s.mem base a k then 1 else 0) ∧
      Kp [.r6, .r7, .r8] s u ∧ u.mem = s.mem
  | 0, _ => WP.block_nil ⟨by rw [hc]; rfl, Kp.refl _ _, rfl⟩
  | k + 1, hk => by
    rw [ltDigits_succ]
    refine wp_append (WP.mono (ltDigits_ok hs h3 h0 hc ha hm (k := k) (by omega)) fun s₁ ⟨c₁, K₁, m₁⟩ => ?_)
    refine WP.mono (ltDigit_ok (K₁.ws hs) (K₁.at h3) (by rw [K₁.g]; exact h0)
      (by rw [c₁]; split <;> decide) (j := k) (by omega) (by omega)) fun u ⟨c₂, K₂, m₂⟩ =>
        ⟨?_, K₁.trans K₂, m₂.trans m₁⟩
    rw [c₂, c₁, m₁]
    have t0 := w32_lt s.mem base (a + 4 * k)
    have t1 := w32_lt s.mem base (m + 4 * k)
    have hM := val32_lt s.mem base m k
    have hA := val32_lt s.mem base a k
    rw [val32_append s.mem base m k 1, val32_append s.mem base a k 1]
    simp only [val32, Nat.mul_zero, Nat.add_zero]
    have hle := lt_top (x := w32 s.mem base (m + 4 * k)) (y := w32 s.mem base (a + 4 * k)) hM hA
    by_cases h1 : val32 s.mem base m k ≤ val32 s.mem base a k <;>
      by_cases h2 : val32 s.mem base m k + 2 ^ (32 * k) * w32 s.mem base (m + 4 * k) ≤
        val32 s.mem base a k + 2 ^ (32 * k) * w32 s.mem base (a + 4 * k) <;>
      simp only [h1, h2, ite_true, ite_false] <;> omega

/-- `r5` is all ones iff `[a] < [m]` (`n` words each). -/
theorem ltM_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {m a : Nat} (ha : a + 8 * c.n ≤ size) (hm : m + 8 * c.n ≤ size) :
    WP isa (.block (c.ltM m a)) s fun s' =>
      s'.gpr .r5 = mask64 (wordsVal s.mem base a c.n < wordsVal s.mem base m c.n) ∧
      Kp [.r0, .r5, .r6, .r7, .r8] s s' ∧ s'.mem = s.mem := by
  rw [Cfg.ltM, List.append_assoc]
  refine mask32_ok ?_
  show WP isa (.block (.li .r6 1 :: (ltDigits m a (2 * c.n) ++ [.subi .r5 .r6 1]))) _ _
  refine wp_step (exec_li (by decide)) ?_
  refine wp_append (WP.mono (ltDigits_ok ((hs.write _ _).write _ _) ((h3.write _).write _)
    (by simp only [write_gpr, reduceCtorEq, ite_false, ite_true]) (by simp only [write_gpr, ite_true])
    (m := m) (a := a) (W := 2 * c.n) (by omega) (by omega) (k := 2 * c.n) (Nat.le_refl _))
    fun s₁ ⟨c₁, K₁, m₁⟩ => ?_)
  simp only [write_mem, ← wordsVal_eq_val32] at c₁ m₁
  refine wp_step (exec_subi (by decide) (by decide)) (WP.block_nil ⟨?_, ?_, by simp only [write_mem]; exact m₁⟩)
  · simp only [write_gpr, ite_true]
    have e : s₁.gpr .r6 = BitVec.ofNat 64 (if wordsVal s.mem base m c.n ≤ wordsVal s.mem base a c.n then 1 else 0) := by
      apply BitVec.eq_of_toNat_eq; rw [c₁]; split <;> rfl
    rw [e]
    by_cases h : wordsVal s.mem base m c.n ≤ wordsVal s.mem base a c.n
    · have h' : ¬ wordsVal s.mem base a c.n < wordsVal s.mem base m c.n := by omega
      simp only [h, h', ite_true, ite_false, mask64]; decide
    · have h' : wordsVal s.mem base a c.n < wordsVal s.mem base m c.n := by omega
      simp only [h, h', ite_true, ite_false, mask64]; decide
  · exact ((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (K₁.mono (by decide))).trans
      (Kp.write _ _ (by decide)))

/-! ## The flag -/

/-- The flag `&=` the mask `r5`. -/
theorem andFlag_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    (hF : c.sl FLAG + 8 ≤ size) :
    WP isa (.block c.andFlag) s fun s' =>
      flagW c base s' = flagW c base s &&& s.gpr .r5 ∧ Kp [.r4] s s' ∧
      s'.mem = s.mem.writeW (off base (c.sl FLAG)) (flagW c base s &&& s.gpr .r5) := by
  simp only [Cfg.andFlag]
  refine wp_step (ld0_ok hs h3 (by decide) (sl_al c FLAG) hF) ?_
  refine wp_step exec_logic ?_
  refine wp_step (std0_ok ((hs.write _ _).write _ _) ((h3.write _).write _) (by decide) (sl_al c FLAG) hF)
    (WP.block_nil ⟨?_, ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.store _ _ _), ?_⟩)
  · simp only [write_mem, write_gpr, ite_true, reduceCtorEq, ite_false, flagW, word_writeW_self]
  · simp only [write_mem, write_gpr, ite_true, reduceCtorEq, ite_false, flagW]

/-- `[a]` in `[1, n - 1]`: the flag `&=` its mask. -/
theorem checkRange_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Ws s base size)
    (h3 : At s base .r3 0) {a : Nat} (ha4 : a % 4 = 0) (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size)
    (hmn : c.sl MN + 8 * c.n ≤ size) (hF : c.sl FLAG + 8 ≤ size) :
    WP isa (.block (c.checkRange a)) s fun s' =>
      flagW c base s' = flagW c base s &&&
        mask64 (0 < wordsVal s.mem base a c.n ∧ wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MN) c.n) ∧
      Kp [.r0, .r4, .r5, .r6, .r7, .r8, .r9] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [Cfg.checkRange, Cfg.ltN, List.append_assoc, List.append_assoc, List.append_assoc]
  refine wp_append (WP.mono (ltM_ok c hs h3 ha hmn) fun s₁ ⟨g₁, K₁, m₁⟩ => ?_)
  rw [List.singleton_append]
  refine wp_step exec_mov ?_
  refine wp_append (WP.mono (nonzero_ok c ((K₁.ws hs).write _ _) ((K₁.at h3).write _) ha4 hn ha)
    fun s₂ ⟨g₂, K₂, m₂⟩ => ?_)
  simp only [write_mem, m₁] at g₂ m₂
  rw [List.singleton_append]
  refine wp_step exec_logic ?_
  have K₃ : Kp [.r0, .r4, .r5, .r6, .r7, .r8, .r9] s
      (s₂.write .r5 (s₂.gpr .r5 &&& s₂.gpr .r9)) :=
    (((K₁.mono (by decide)).trans (Kp.write _ _ (by decide))).trans (K₂.mono (by decide))).trans
      (Kp.write _ _ (by decide))
  refine WP.mono (andFlag_ok c (K₃.ws hs) (K₃.at h3) hF) fun s' ⟨f', k', m'⟩ => ⟨?_, K₃.trans (k'.mono (by decide)), ?_⟩
  · rw [f']
    simp only [flagW, write_mem, write_gpr, ite_true, m₂, g₂]
    rw [K₂.gpr _ (by decide)]
    simp only [write_gpr, ite_true, g₁, mask64_and]
    congr 1
    by_cases h1 : 0 < wordsVal s.mem base a c.n <;> by_cases h2 : wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MN) c.n <;>
      simp [mask64, h1, h2, Nat.pos_iff_ne_zero.mp] <;> omega
  · rw [m']
    simp only [write_mem, m₂]
    exact writeW_outside _ _ _ (by omega)

/-- `[a] ≠ 0`: the flag `&=` its mask. -/
theorem checkNonzero_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Ws s base size)
    (h3 : At s base .r3 0) {a : Nat} (ha4 : a % 4 = 0) (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size)
    (hF : c.sl FLAG + 8 ≤ size) :
    WP isa (.block (c.checkNonzero a)) s fun s' =>
      flagW c base s' = flagW c base s &&& mask64 (wordsVal s.mem base a c.n ≠ 0) ∧
      Kp [.r4, .r5] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [Cfg.checkNonzero]
  refine wp_append (WP.mono (nonzero_ok c hs h3 ha4 hn ha) fun s₁ ⟨g₁, K₁, m₁⟩ => ?_)
  refine WP.mono (andFlag_ok c (K₁.ws hs) (K₁.at h3) hF) fun s' ⟨f', k', m'⟩ =>
    ⟨?_, K₁.trans (k'.mono (by decide)), ?_⟩
  · rw [f', g₁]; simp only [flagW, m₁]
  · rw [m', m₁]; exact writeW_outside _ _ _ (by omega)

end VG.Proof.Ecdsa.PPC64LE
