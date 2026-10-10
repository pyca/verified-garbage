import VerifiedGarbage.Proof.Weierstrass.Arm.Bytes
import VerifiedGarbage.Impl.Ecdsa.Arm

/-!
# ECDSA on 32-bit ARM: the masks of the checks, and the flag

The checks of `Impl/Ecdsa/Arm.lean` as masks, all ones or zero:
`nonzero a` sets `r5` to all ones iff `[a] ≠ 0` (`nonzero_ok`: the words
or'ed, then the top bit of `-x | x`), `ltM m a` sets `r5` to all ones iff
`[a] < [m]` (`ltM_ok`: the carry out of `[a] - [m]`, digit by digit; `ltN`
is `ltM` for `MN`), and
`andFlag` ands `r5` into the flag word (`andFlag_ok`); so `checkRange a` ands
the mask of `0 < [a] < [MN]` into the flag (`checkRange_ok`) and
`checkNonzero a` the mask of `[a] ≠ 0` (`checkNonzero_ok`).
-/

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Ecdsa.Arm VG.Proof.Mont.Arm
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_ldr wp_str wp_dp wp_mov wp_movw op2_reg op2_imm op2_lsr dpVal
  toNat_add_lt toNat_shr)

/-- A mask: all ones if `p`, else zero. -/
abbrev mask32 (p : Prop) [Decidable p] : BitVec 32 := if p then BitVec.allOnes 32 else 0

theorem mask32_and (p q : Prop) [Decidable p] [Decidable q] : mask32 p &&& mask32 q = mask32 (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;>
    simp only [mask32, hp, hq, ite_true, ite_false, and_self, and_false, false_and] <;> decide

/-- The flag word. -/
abbrev flagW (c : Cfg) (base : Addr) (s : State) : BitVec 32 := s.mem.readW (off base (c.sl FLAG)) 32

/-! ## Nonzero -/

/-- One `or` of `nonzero`. -/
def orStep (a j : Nat) : List Instr := [.ldr .r4 wb (a + 4 * (j + 1)), .dp .orr .r5 .r5 (.reg .r4)]

theorem nonzero_eq (c : Cfg) (a : Nat) : c.nonzero a = ([.ldr .r5 wb a] : List Instr) ++
    (List.range (2 * c.n - 1)).flatMap (orStep a) ++
    ([.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.reg .r5), .dp .orr .r4 .r4 (.reg .r5),
      .mov .r4 (.shifted .r4 .lsr 31), .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.reg .r4)] : List Instr) :=
  rfl

theorem w32_eq_zero_iff (m : Mem) (base : Addr) (d : Nat) :
    (m.readW (off base d) 32 = 0) ↔ w32 m base d = 0 :=
  ⟨fun h => by simp [w32, h], fun h => BitVec.eq_of_toNat_eq h⟩

/-- The `or`s of `nonzero`. -/
theorem ors_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat} :
    ∀ k, a + 4 * (k + 1) ≤ size →
    WP isa (.block ((List.range k).flatMap (orStep a))) s fun s' =>
      (s'.gpr .r5 = 0 ↔ s.gpr .r5 = 0 ∧ ∀ j < k, w32 s.mem base (a + 4 * (j + 1)) = 0) ∧
      Rest [.r4, .r5] s s' ∧ s'.mem = s.mem
  | 0, _ => WP.block_nil ⟨⟨fun h => ⟨h, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩, fun h => h.1⟩,
      Rest.refl _ _, rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine VG.Proof.X25519.Arm.WP.append (ors_ok hs k (by omega_arith)) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_
    have hs₁ := hs.of_rest k₁ (by decide)
    rw [orStep]
    refine wp_ldr (hs.off_lt (by omega_arith)) (hs₁.ea (by omega_arith)) (hs₁.read (d := a + 4 * (k + 1)) (n := 4) (by omega_arith))
      fun s₂ u₂ => ?_
    refine wp_dp (op2_reg _ _) fun s₃ u₃ => WP.block_nil
      ⟨?_, k₁.trans ((u₂.rest (by simp)).trans (u₃.rest (by simp))), by rw [u₃.mem, u₂.mem, m₁]⟩
    have hor : ∀ x y : BitVec 32, x ||| y = 0 ↔ x = 0 ∧ y = 0 := fun _ _ => BitVec.or_eq_zero_iff
    rw [u₃.gpr, dpVal, hor, u₂.other _ (by decide), e₁, u₂.gpr, m₁, w32_eq_zero_iff]
    constructor
    · intro ⟨⟨h₀, h⟩, hw⟩
      refine ⟨h₀, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j k with hj' | hj'
      · exact h j hj'
      · obtain rfl : j = k := by omega_arith
        exact hw
    · intro ⟨h₀, h⟩
      exact ⟨⟨h₀, fun j hj => h j (by omega_arith)⟩, h k (by omega_arith)⟩

/-- The top bit of `-x | x` is whether `x ≠ 0`. -/
theorem negOr_shr (x : BitVec 32) : ((0 - x) ||| x) >>> 31 = if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · subst hx; decide
  · rw [ite_eq_right hx]
    apply BitVec.eq_of_toNat_eq
    have h0 : x.toNat ≠ 0 := fun e => hx (BitVec.eq_of_toNat_eq e)
    have hlt := ((0 - x) ||| x).isLt
    have h1 : (0 - x).toNat ≤ ((0 - x) ||| x).toNat := by rw [BitVec.toNat_or]; exact Nat.left_le_or
    have h2 : x.toNat ≤ ((0 - x) ||| x).toNat := by rw [BitVec.toNat_or]; exact Nat.right_le_or
    have h3 : (0 - x).toNat = 2 ^ 32 - x.toNat := by
      have h00 : (0 : BitVec 32).toNat = 0 := rfl
      rw [BitVec.toNat_sub, h00]; have := x.isLt; omega_arith
    rw [toNat_shr]
    show _ = 1
    omega_arith

theorem neg_bit32 (b : Bool) : (0 : BitVec 32) - (if b then 1 else 0) = mask32 (b = true) := by
  cases b <;> decide

/-- `r5` is all ones iff `[a] ≠ 0`; `r4` changes too. -/
theorem nonzero_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) :
    WP isa (.block (c.nonzero a)) s fun s' =>
      s'.gpr .r5 = mask32 (wordsVal s.mem base a c.n ≠ 0) ∧ Rest [.r4, .r5] s s' ∧ s'.mem = s.mem := by
  rw [nonzero_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_ldr (hs.off_lt (by omega_arith)) (hs.ea (by omega_arith)) (hs.read (d := a) (n := 4) (by omega_arith)) fun s₁ u₁ => ?_
  have hs₁ := hs.of_rest (u₁.rest (ws := [.r4, .r5]) (by simp)) (by decide)
  refine VG.Proof.X25519.Arm.WP.append (ors_ok hs₁ (2 * c.n - 1) (by omega_arith)) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_
  rw [u₁.gpr, u₁.mem] at e₂
  have hz : s₂.gpr .r5 = 0 ↔ wordsVal s.mem base a c.n = 0 := by
    rw [e₂, wordsVal_eq_val32, val32_eq_zero_iff, w32_eq_zero_iff]
    constructor
    · intro ⟨h₀, h⟩ j hj
      rcases j with _ | j
      · simpa using h₀
      · exact h j (by omega_arith)
    · intro h
      exact ⟨by simpa using h 0 (by omega_arith), fun j hj => h (j + 1) (by omega_arith)⟩
  refine wp_mov (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₆ u₆ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₇ u₇ => ?_
  refine wp_dp (op2_reg _ _) fun s₈ u₈ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have r5₅ : s₅.gpr .r5 = s₂.gpr .r5 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
    have r4₆ : s₆.gpr .r4 = if s₂.gpr .r5 = 0 then 0 else 1 := by
      rw [u₆.gpr, u₅.gpr, dpVal, u₄.gpr, dpVal, u₃.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        r5₅.symm.trans r5₅, ← r5₅, negOr_shr, r5₅]
    rw [u₈.gpr, dpVal, u₇.gpr, u₇.other _ (by decide), r4₆]
    have : (if s₂.gpr .r5 = 0 then (0 : BitVec 32) else 1) = if decide (s₂.gpr .r5 ≠ 0) then 1 else 0 := by
      by_cases h : s₂.gpr .r5 = 0 <;> simp [h]
    rw [this, neg_bit32]
    simp only [mask32, decide_eq_true_eq, ne_eq, hz]
  · exact ((u₁.rest (by simp)).trans k₂).trans ((u₃.rest (by simp)).trans ((u₄.rest (by simp)).trans
      ((u₅.rest (by simp)).trans ((u₆.rest (by simp)).trans ((u₇.rest (by simp)).trans (u₈.rest (by simp)))))))
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem]

/-! ## Less than the order -/

/-- The arithmetic of a word of the comparison: the low part `T` and the
carry `c` of `A + 2^(32k) - N` (from the carry in `c₀`), a word on. -/
theorem lt_word_step {P T c c1 c2 c0 a0 a1 n0 n1 A N d0 d1 : Nat} (hT : T < P) (hd0 : d0 < 2 ^ 16)
    (hd1 : d1 < 2 ^ 16) (hn0 : n0 < 2 ^ 16) (hn1 : n1 < 2 ^ 16)
    (h : T + P * c + N + 1 = A + P + c0)
    (h0 : d0 + 2 ^ 16 * c1 = a0 + (2 ^ 16 - 1 - n0) + c) (h1 : d1 + 2 ^ 16 * c2 = a1 + (2 ^ 16 - 1 - n1) + c1) :
    T + P * (d0 + 2 ^ 16 * d1) < P * 2 ^ 32 ∧
    T + P * (d0 + 2 ^ 16 * d1) + P * 2 ^ 32 * c2 + (N + P * (n0 + 2 ^ 16 * n1)) + 1 =
      A + P * (a0 + 2 ^ 16 * a1) + P * 2 ^ 32 + c0 := by
  have hw : d0 + 2 ^ 16 * d1 + 2 ^ 32 * c2 + (n0 + 2 ^ 16 * n1) + 1 = a0 + 2 ^ 16 * a1 + 2 ^ 32 + c := by omega_arith
  have hb : d0 + 2 ^ 16 * d1 + 1 ≤ 2 ^ 32 := by omega_arith
  have hb' := Nat.mul_le_mul_left P hb
  constructor
  · rw [Nat.mul_add, Nat.mul_one] at hb'; omega_arith
  · have := congrArg (P * ·) hw
    simp only [Nat.mul_add, Nat.mul_one] at this
    grind

/-- The carry of digit `j` of `[a] - n`, with `r7` and `r8` their words. -/
theorem ltDigit_ok {s : State} {j : Nat} (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16)
    (hc : (s.gpr .r3).toNat ≤ 1) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, (u.gpr .r3).toNat = (hdig (s.gpr .r7).toNat (j % 2) +
        (2 ^ 16 - 1 - hdig (s.gpr .r8).toNat (j % 2)) + (s.gpr .r3).toNat) / 2 ^ 16 →
      Rest [.r3, .r4, .r5] s u → u.mem = s.mem → WP isa (.block is) u Q) :
    WP isa (.block (Cfg.ltDigit j ++ is)) s Q := by
  simp only [Cfg.ltDigit, List.cons_append, List.nil_append]
  refine wp_half (Nat.mod_lt _ (by decide)) h6 fun s₁ u₁ => ?_
  refine wp_half (Nat.mod_lt _ (by decide)) (by rw [u₁.other _ (by decide)]; exact h6) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₆ u₆ => ?_
  have d0 := hdig_lt (s.gpr .r7).toNat (j % 2)
  have d1 := hdig_lt (s.gpr .r8).toNat (j % 2)
  have a1 : (s₁.gpr .r4).toNat = hdig (s.gpr .r7).toNat (j % 2) := by rw [u₁.gpr, BitVec.toNat_ofNat]; omega_arith
  have a2 : (s₂.gpr .r5).toNat = hdig (s.gpr .r8).toNat (j % 2) := by
    rw [u₂.gpr, u₁.other _ (by decide), BitVec.toNat_ofNat]; omega_arith
  have h6₂ : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact h6
  have a3 : (s₃.gpr .r4).toNat = hdig (s.gpr .r7).toNat (j % 2) + (2 ^ 16 - 1) := by
    rw [u₃.gpr, dpVal, u₂.other _ (by decide), toNat_add_lt (by rw [a1, h6₂, toNat_mask16]; omega_arith), a1, h6₂,
      toNat_mask16]
  have a3r5 : s₃.gpr .r5 = s₂.gpr .r5 := u₃.other _ (by decide)
  have a4 : (s₄.gpr .r4).toNat = hdig (s.gpr .r7).toNat (j % 2) + (2 ^ 16 - 1 - hdig (s.gpr .r8).toNat (j % 2)) := by
    rw [u₄.gpr, dpVal, VG.Proof.X25519.Arm.toNat_sub_le (by rw [a3, a3r5, a2]; omega_arith), a3, a3r5, a2]; omega_arith
  have a4r3 : s₄.gpr .r3 = s.gpr .r3 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have a5 : (s₅.gpr .r4).toNat = hdig (s.gpr .r7).toNat (j % 2) +
      (2 ^ 16 - 1 - hdig (s.gpr .r8).toNat (j % 2)) + (s.gpr .r3).toNat := by
    rw [u₅.gpr, dpVal, toNat_add_lt (by rw [a4, a4r3]; omega_arith), a4, a4r3]
  refine k s₆ (by rw [u₆.gpr, toNat_shr, a5]) ?_
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
  exact (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans
    ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp))))))

/-- Word `k` of the comparison of `[a]` with `[m]`. -/
def ltWord (a m k : Nat) : List Instr :=
  [.ldr .r7 wb (a + 4 * k), .ldr .r8 wb (m + 4 * k)] ++ Cfg.ltDigit (2 * k) ++ Cfg.ltDigit (2 * k + 1)

theorem ltM_eq (c : Cfg) (m a : Nat) :
    c.ltM m a = ([mask16, .mov .r3 (.imm 1)] : List Instr) ++ (List.range (2 * c.n)).flatMap (ltWord a m) ++
      ([.dp .sub .r5 .r3 (.imm 1)] : List Instr) :=
  rfl

/-- The carry of the first `k` words of `[a] - [m]`, from the carry `c₀`:
`T + 2^(32k) c + M + 1 = A + 2^(32k) + c₀` for some `T < 2^(32k)`. -/
theorem ltK_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a m : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hc : (s.gpr .r3).toNat ≤ 1) :
    ∀ k, a + 4 * k ≤ size → m + 4 * k ≤ size →
    WP isa (.block ((List.range k).flatMap (ltWord a m))) s fun u =>
      (u.gpr .r3).toNat ≤ 1 ∧
      (∃ T, T < 2 ^ (32 * k) ∧ T + 2 ^ (32 * k) * (u.gpr .r3).toNat + val32 s.mem base m k + 1 =
        val32 s.mem base a k + 2 ^ (32 * k) + (s.gpr .r3).toNat) ∧
      Rest [.r3, .r4, .r5, .r7, .r8] s u ∧ u.mem = s.mem
  | 0, _, _ => WP.block_nil ⟨hc, ⟨0, by decide, by simp only [val32, Nat.mul_zero, Nat.pow_zero]; omega_arith⟩,
      Rest.refl _ _, rfl⟩
  | k + 1, ha, hm => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine VG.Proof.X25519.Arm.WP.append (ltK_ok hs h6 hc k (by omega_arith) (by omega_arith))
      fun s₁ ⟨C₁, ⟨T, hT, V₁⟩, K₁, m₁⟩ => ?_
    have hs₁ := hs.of_rest K₁ (by decide)
    simp only [ltWord, List.cons_append, List.append_assoc]
    refine wp_ldr (hs.off_lt (by omega_arith)) (hs₁.ea (by omega_arith)) (hs₁.read (d := a + 4 * k) (n := 4) (by omega_arith))
      fun s₂ u₂ => ?_
    have hs₂ := hs₁.of_rest (u₂.rest (ws := [.r7]) (by simp)) (by decide)
    refine wp_ldr (hs.off_lt (by omega_arith)) (hs₂.ea (by omega_arith)) (hs₂.read (d := m + 4 * k) (n := 4) (by omega_arith))
      fun s₃ u₃ => ?_
    have K₃ : Rest [.r3, .r4, .r5, .r7, .r8] s s₃ := K₁.trans ((u₂.rest (by simp)).trans (u₃.rest (by simp)))
    refine ltDigit_ok (j := 2 * k) (by rw [K₃.gpr _ (by decide)]; exact h6)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide)]; exact C₁) fun s₄ c₄ K₄ m₄ => ?_
    have h6₄ : s₄.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
      rw [K₄.gpr _ (by decide), K₃.gpr _ (by decide)]; exact h6
    have hwa : (s₂.gpr .r7).toNat = w32 s.mem base (a + 4 * k) := by rw [u₂.gpr, m₁]
    have hwm : (s₃.gpr .r8).toNat = w32 s.mem base (m + 4 * k) := by rw [u₃.gpr, u₂.mem, m₁]
    have r7₃ : s₃.gpr .r7 = s₂.gpr .r7 := u₃.other _ (by decide)
    have r3₃ : s₃.gpr .r3 = s₁.gpr .r3 := by rw [u₃.other _ (by decide), u₂.other _ (by decide)]
    rw [r7₃, hwa, hwm, r3₃, show 2 * k % 2 = 0 by omega_arith] at c₄
    have hd0 := hdig_lt (w32 s.mem base (a + 4 * k)) 0
    have hn0 := hdig_lt (w32 s.mem base (m + 4 * k)) 0
    refine ltDigit_ok (j := 2 * k + 1) h6₄ (by rw [c₄]; omega_arith) fun u c₅ K₅ m₅ => WP.block_nil ?_
    rw [K₄.gpr _ (by decide), K₄.gpr _ (by decide), r7₃, hwa, hwm, show (2 * k + 1) % 2 = 1 by omega_arith] at c₅
    have hd1 := hdig_lt (w32 s.mem base (a + 4 * k)) 1
    have hn1 := hdig_lt (w32 s.mem base (m + 4 * k)) 1
    have ea := word_digits (w32 s.mem base (a + 4 * k)) (BitVec.isLt _)
    have em := word_digits (w32 s.mem base (m + 4 * k)) (BitVec.isLt _)
    refine ⟨by rw [c₅]; omega_arith, ?_, K₃.trans ((K₄.mono (by simp)).trans (K₅.mono (by simp))),
      by rw [m₅, m₄, u₃.mem, u₂.mem, m₁]⟩
    generalize hdig (w32 s.mem base (a + 4 * k)) 0 = a0 at *
    generalize hdig (w32 s.mem base (a + 4 * k)) 1 = a1 at *
    generalize hdig (w32 s.mem base (m + 4 * k)) 0 = n0 at *
    generalize hdig (w32 s.mem base (m + 4 * k)) 1 = n1 at *
    generalize ex0 : a0 + (2 ^ 16 - 1 - n0) + (s₁.gpr .r3).toNat = x0 at c₄
    generalize ex1 : a1 + (2 ^ 16 - 1 - n1) + (s₄.gpr .r3).toNat = x1 at c₅
    have h0 : x0 % 2 ^ 16 + 2 ^ 16 * (s₄.gpr .r3).toNat = a0 + (2 ^ 16 - 1 - n0) + (s₁.gpr .r3).toNat := by
      rw [c₄, ex0]; omega_arith
    have h1 : x1 % 2 ^ 16 + 2 ^ 16 * (u.gpr .r3).toNat = a1 + (2 ^ 16 - 1 - n1) + (s₄.gpr .r3).toNat := by
      rw [c₅, ex1]; omega_arith
    obtain ⟨hlt, heq⟩ := lt_word_step (P := 2 ^ (32 * k)) hT (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
      hn0 hn1 V₁ h0 h1
    refine ⟨_, by rw [show 32 * (k + 1) = 32 * k + 32 by omega_arith, Nat.pow_add]; exact hlt, ?_⟩
    rw [val32_append _ _ _ k 1, val32_append _ _ _ k 1, show 32 * (k + 1) = 32 * k + 32 by omega_arith, Nat.pow_add]
    simp only [val32, Nat.mul_zero, Nat.add_zero]
    rw [ea, em, Nat.mul_comm a1, Nat.mul_comm n1]
    exact heq

/-- `r5` is all ones iff `[a] < [m]`; `r3`, `r4`, `r6`, `r7` and `r8` change too. -/
theorem ltM_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {m a : Nat}
    (ha : a + 8 * c.n ≤ size) (hm : m + 8 * c.n ≤ size) :
    WP isa (.block (c.ltM m a)) s fun s' =>
      s'.gpr .r5 = mask32 (wordsVal s.mem base a c.n < wordsVal s.mem base m c.n) ∧
      Rest [.r3, .r4, .r5, .r6, .r7, .r8] s s' ∧ s'.mem = s.mem := by
  rw [ltM_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_movw fun s₁ u₁ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have K₂ : Rest [.r3, .r4, .r5, .r6, .r7, .r8] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  have hs₂ := hs.of_rest K₂ (by decide)
  have c₂ : (s₂.gpr .r3).toNat = 1 := by rw [u₂.gpr]; rfl
  refine VG.Proof.X25519.Arm.WP.append (ltK_ok hs₂ (a := a) (m := m)
    (by rw [u₂.other _ (by decide), u₁.gpr]) (by omega_arith) (2 * c.n) (by omega_arith) (by omega_arith))
    fun s₃ ⟨C₃, ⟨T, hT, V₃⟩, K₃, m₃⟩ => ?_
  have mem₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  rw [c₂, mem₂] at V₃
  refine wp_dp (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ⟨?_, K₂.trans ((K₃.mono (by simp)).trans
    (u₄.rest (by simp))), by rw [u₄.mem, m₃, mem₂]⟩
  have hA := val32_lt s.mem base a (2 * c.n)
  have hN := val32_lt s.mem base m (2 * c.n)
  rw [u₄.gpr, dpVal, wordsVal_eq_val32, wordsVal_eq_val32]
  generalize 2 ^ (32 * (2 * c.n)) = P at *
  have hr3 : s₃.gpr .r3 = if val32 s.mem base a (2 * c.n) < val32 s.mem base m (2 * c.n) then 0 else 1 := by
    apply BitVec.eq_of_toNat_eq
    obtain h | h : (s₃.gpr .r3).toNat = 0 ∨ (s₃.gpr .r3).toNat = 1 := by omega_arith
    · rw [h, Nat.mul_zero] at V₃
      rw [h, ite_eq_left (by omega_arith)]; rfl
    · rw [h, Nat.mul_one] at V₃
      rw [h, ite_eq_right (by omega_arith)]; rfl
  rw [hr3]
  split <;> decide

/-- `r5` is all ones iff `[a] < [MN]`; `r3`, `r4`, `r6`, `r7` and `r8` change too. -/
theorem ltN_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (ha : a + 8 * c.n ≤ size) (hm : c.sl MN + 8 * c.n ≤ size) :
    WP isa (.block (c.ltN a)) s fun s' =>
      s'.gpr .r5 = mask32 (wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MN) c.n) ∧
      Rest [.r3, .r4, .r5, .r6, .r7, .r8] s s' ∧ s'.mem = s.mem :=
  ltM_ok c hs ha hm

/-! ## The flag -/

/-- `[FLAG] &= r5`, through `r4`. -/
theorem andFlag_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hf : c.sl FLAG + 4 ≤ size) :
    WP isa (.block c.andFlag) s fun s' =>
      flagW c base s' = flagW c base s &&& s.gpr .r5 ∧
      Rest [.r4] s s' ∧ Outside base (c.sl FLAG) 4 s.mem s'.mem := by
  simp only [Cfg.andFlag]
  refine wp_ldr (hs.off_lt (by omega_arith)) (hs.ea (by omega_arith)) (hs.read hf) fun s₁ u₁ => ?_
  refine wp_dp (op2_reg _ _) fun s₂ u₂ => ?_
  have k₂ : Rest [.r4] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  have hs₂ := hs.of_rest k₂ (by decide)
  refine wp_str (hs.off_lt (by omega_arith)) (hs₂.ea (d := c.sl FLAG) (by omega_arith)) (hs₂.write hf) fun s₃ m₃ =>
    WP.block_nil ⟨?_, k₂.trans (m₃.rest _), ?_⟩
  · rw [flagW, flagW, m₃.mem, Mem.readW_writeW_self32, u₂.gpr, dpVal, u₁.gpr, u₁.other _ (by decide)]
  · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by have := hs.nowrap; omega_arith)

/-- `checkRange a`: the flag `&=` the mask of `0 < [a] < [MN]`. -/
theorem checkRange_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hm : c.sl MN + 8 * c.n ≤ size) (hf : c.sl FLAG + 4 ≤ size) :
    WP isa (.block (c.checkRange a)) s fun s' =>
      flagW c base s' = flagW c base s &&&
        mask32 (0 < wordsVal s.mem base a c.n ∧ wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MN) c.n) ∧
      Rest [.r3, .r4, .r5, .r6, .r7, .r8, .r9] s s' ∧ Outside base (c.sl FLAG) 4 s.mem s'.mem := by
  simp only [Cfg.checkRange, List.append_assoc, List.singleton_append]
  refine VG.Proof.X25519.Arm.WP.append (ltN_ok c hs ha hm) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => ?_
  have k₂ : Rest [.r3, .r4, .r5, .r6, .r7, .r8, .r9] s s₂ := (k₁.mono (by simp)).trans (u₂.rest (by simp))
  have hs₂ := hs.of_rest k₂ (by decide)
  refine VG.Proof.X25519.Arm.WP.append (nonzero_ok c hs₂ hn ha) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  have k₄ : Rest [.r3, .r4, .r5, .r6, .r7, .r8, .r9] s s₄ := k₂.trans ((k₃.mono (by simp)).trans (u₄.rest (by simp)))
  have hs₄ := hs.of_rest k₄ (by decide)
  have mem₄ : s₄.mem = s.mem := by rw [u₄.mem, m₃, u₂.mem, m₁]
  refine WP.mono (andFlag_ok c hs₄ hf) fun s₅ ⟨e₅, k₅, O₅⟩ =>
    ⟨?_, k₄.trans (k₅.mono (by simp)), by rw [← mem₄]; exact O₅⟩
  rw [e₅, flagW, flagW, mem₄, u₄.gpr, dpVal, e₃, k₃.gpr _ (by decide), u₂.gpr, e₁,
    u₂.mem, m₁, BitVec.and_comm (mask32 _), mask32_and]
  simp only [Nat.pos_iff_ne_zero, and_comm]

/-- `checkNonzero a`: the flag `&=` the mask of `[a] ≠ 0`. -/
theorem checkNonzero_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hf : c.sl FLAG + 4 ≤ size) :
    WP isa (.block (c.checkNonzero a)) s fun s' =>
      flagW c base s' = flagW c base s &&& mask32 (wordsVal s.mem base a c.n ≠ 0) ∧
      Rest [.r4, .r5] s s' ∧ Outside base (c.sl FLAG) 4 s.mem s'.mem := by
  rw [Cfg.checkNonzero]
  refine VG.Proof.X25519.Arm.WP.append (nonzero_ok c hs hn ha) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_
  refine WP.mono (andFlag_ok c (hs.of_rest k₁ (by decide)) hf) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  exact ⟨by rw [e₂, e₁, flagW, flagW, m₁], k₁.trans (k₂.mono (by simp)), by rw [← m₁]; exact O₂⟩

end VG.Proof.Ecdsa.Arm
