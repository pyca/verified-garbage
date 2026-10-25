module

public import VerifiedGarbage.Impl.Dsa.Arm.Checks
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Add
public import VerifiedGarbage.Proof.Ecdsa.Arm.Flags
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Digit
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# DSA on 32-bit ARM: the masks of the checks

Each check leaves a mask in `r2`, all ones or zero (`mask32`): `nonzero k a`
of `[a] ≠ 0` (`nonzero_ok`), `lessThan k a b` of `[a] < [b]`
(`lessThan_ok`: the carry of `[a] - [b]` a 16-bit digit at a time, as in
`chain_next`), `equal k a b` of `[a] = [b]`; `subWords k o a b` writes
`[a] - [b]` modulo `2^(32k)` (`subWords_ok`), `setConst k o x` the constant
`x` (`setConst_ok`), and `andFlag` ands `r2` into a flag word.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32 mask32_and negOr_shr neg_bit32 w32_eq_zero_iff)
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp wp_movw op2_imm op2_reg op2_lsr op2_lsl
  dpVal toNat_shr)

/-! ## Arithmetic of the borrow chain -/

/-- A word of `[a] - [b]` from its two digits: `w + 2³² c' + b + 1 = a + 2³² + c`. -/
theorem borrow_word {a0 a1 b0 b1 c x0 x1 : Nat} (ha0 : a0 < 2 ^ 16) (ha1 : a1 < 2 ^ 16) (hb0 : b0 < 2 ^ 16)
    (hb1 : b1 < 2 ^ 16) (hc : c ≤ 1) (h0 : x0 = a0 + (2 ^ 16 - 1 - b0) + c)
    (h1 : x1 = a1 + (2 ^ 16 - 1 - b1) + x0 / 2 ^ 16) :
    x0 % 2 ^ 16 + x1 % 2 ^ 16 * 2 ^ 16 + 2 ^ 32 * (x1 / 2 ^ 16) + (b0 + b1 * 2 ^ 16) + 1 =
      a0 + a1 * 2 ^ 16 + 2 ^ 32 + c ∧ x1 / 2 ^ 16 ≤ 1 := by
  subst h0 h1; omega_arith

/-- The chain a word on: `T + P c + B = A + P` for the low part `T < P`. -/
theorem chain_next {P T c B A w c' wb wa : Nat} (hT : T < P) (hw32 : w < 2 ^ 32) (h : T + P * c + B = A + P)
    (hw : w + 2 ^ 32 * c' + wb + 1 = wa + 2 ^ 32 + c) :
    T + P * w < 2 ^ 32 * P ∧ T + P * w + 2 ^ 32 * P * c' + (B + P * wb) = A + P * wa + 2 ^ 32 * P := by
  constructor
  · have := Nat.mul_le_mul_left P (show w + 1 ≤ 2 ^ 32 by omega_arith)
    rw [Nat.mul_add, Nat.mul_one] at this
    rw [Nat.mul_comm (2 ^ 32)]; omega_arith
  · have := congrArg (P * ·) hw
    simp only [Nat.mul_add, Nat.mul_one] at this
    grind

/-- The chain's carry is whether `A ≥ B`. -/
theorem chain_carry {P T c A B : Nat} (hT : T < P) (hc : c ≤ 1)
    (h : T + P * c + B = A + P) : c = if A < B then 0 else 1 := by
  obtain rfl | rfl : c = 0 ∨ c = 1 := by omega_arith
  · rw [Nat.mul_zero] at h; rw [ite_eq_left (by omega_arith)]
  · rw [Nat.mul_one] at h; rw [ite_eq_right (by omega_arith)]

/-- The chain's low part is `A - B` modulo `P`. -/
theorem chain_low {P T c A B : Nat} (hT : T < P) (hc : c ≤ 1) (h : T + P * c + B = A + P) :
    T = (A + P - B) % P := by
  obtain rfl | rfl : c = 0 ∨ c = 1 := by omega_arith
  · rw [Nat.mul_zero] at h; rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · rw [Nat.mul_one] at h
    rw [show A + P - B = (A - B) + P by omega_arith, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

/-! ## A digit of the difference -/

/-- Digit `h` of `[a] - [b]`: `r4 = a_h + (2¹⁶ - 1 - b_h) + c` for the words in
`r7` and `r5`, its carry to `r3`. -/
theorem borrowDigit_ok {s : State} {h : Nat} (hh : h < 2) (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16)
    (hc : (s.gpr .r3).toNat ≤ 1) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, (u.gpr .r4).toNat = hdig (s.gpr .r7).toNat h + (2 ^ 16 - 1 - hdig (s.gpr .r5).toNat h) +
        (s.gpr .r3).toNat → (u.gpr .r3).toNat = (u.gpr .r4).toNat / 2 ^ 16 → Rest [.r0, .r3, .r4] s u →
      u.mem = s.mem → WP isa (.block is) u Q) :
    WP isa (.block (borrowDigit h ++ is)) s Q := by
  have ha := hdig_lt (s.gpr .r7).toNat h
  have hb := hdig_lt (s.gpr .r5).toNat h
  simp only [borrowDigit, List.cons_append, List.nil_append]
  refine wp_half hh h6 fun s₁ u₁ => wp_dp (op2_reg _ _) fun s₂ u₂ => ?_
  refine wp_half hh (by simp only [u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; exact h6) fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₆ u₆ => ?_
  have v5 : (s₅.gpr .r4).toNat = hdig (s.gpr .r7).toNat h + (2 ^ 16 - 1 - hdig (s.gpr .r5).toNat h) +
      (s.gpr .r3).toNat := by
    simp only [u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, dpVal, h6]
    refine (toNat_add_eq (toNat_sub_eq (toNat_add_eq (toNat_ofNat_dig _ _) toNat_mask16 ?_)
      (toNat_ofNat_dig _ _) ?_) rfl ?_).trans ?_ <;> omega_arith
  refine k s₆ (by rw [u₆.other .r4 (by decide), v5]) (by rw [u₆.gpr, toNat_shr, u₆.other .r4 (by decide)]) ?_
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
  exact (((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp)))).trans
    ((u₅.rest (by simp)).trans (u₆.rest (by simp)))

/-! ## Comparisons -/

/-- The registers the comparisons write: all of `dclob` but `r8`. -/
def ltClob : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .r10]

/-- The borrow chain's invariant after `j` words: `T + 2^(32j) c + B = A + 2^(32j)`. -/
abbrev Chain (m : Mem) (base : Addr) (a b j c : Nat) : Prop :=
  ∃ T, T < 2 ^ (32 * j) ∧ T + 2 ^ (32 * j) * c + val32 m base b j = val32 m base a j + 2 ^ (32 * j)

/-- Two digits of the borrow chain, from the words in `r7` and `r5`. -/
theorem borrowWord {u u₃ u₄ : State} {wa wb : Nat} (r7 : (u.gpr .r7).toNat = wa) (r5 : (u.gpr .r5).toNat = wb)
    (C : (u.gpr .r3).toNat ≤ 1)
    (X₃ : (u₃.gpr .r4).toNat = hdig (u.gpr .r7).toNat 0 + (2 ^ 16 - 1 - hdig (u.gpr .r5).toNat 0) + (u.gpr .r3).toNat)
    (C₃ : (u₃.gpr .r3).toNat = (u₃.gpr .r4).toNat / 2 ^ 16)
    (X₄ : (u₄.gpr .r4).toNat = hdig wa 1 + (2 ^ 16 - 1 - hdig wb 1) + (u₃.gpr .r3).toNat)
    (C₄ : (u₄.gpr .r3).toNat = (u₄.gpr .r4).toNat / 2 ^ 16) (hwa : wa < 2 ^ 32) (hwb : wb < 2 ^ 32) :
    (u₃.gpr .r4).toNat % 2 ^ 16 + (u₄.gpr .r4).toNat % 2 ^ 16 * 2 ^ 16 + 2 ^ 32 * (u₄.gpr .r3).toNat + wb + 1 =
      wa + 2 ^ 32 + (u.gpr .r3).toNat ∧ (u₄.gpr .r3).toNat ≤ 1 := by
  rw [r7, r5] at X₃
  have ea := word_digits wa hwa
  have eb := word_digits wb hwb
  obtain ⟨h, h'⟩ := borrow_word (hdig_lt wa 0) (hdig_lt wa 1) (hdig_lt wb 0) (hdig_lt wb 1) C X₃ (C₃ ▸ X₄)
  rw [C₄]
  exact ⟨by rw [ea, eb]; omega_arith, h'⟩

theorem lessThan_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k a b : Nat} (hk : 0 < k)
    (ha : a + 4 * k ≤ size) (hb : b + 4 * k ≤ size) (h16a : a + 4 * k < 2 ^ 16) (h16b : b < 2 ^ 16) :
    WP isa (lessThan k a b) s fun t =>
      t.gpr .r2 = mask32 (val32 s.mem base a k < val32 s.mem base b k) ∧ Rest ltClob s t ∧ t.mem = s.mem := by
  have hn := hs.nowrap
  unfold lessThan
  refine WP.seq (wp_movw fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_ptr (d := .r10) (by decide) (by omega_arith) fun s₃ u₃ => wp_ptr (d := .r1) (by decide) (by omega_arith) fun s₄ u₄ =>
    wp_ptr (d := .r9) (by decide) (by omega_arith) fun t u₅ => WP.block_nil ?_)
  have R : Rest ltClob s t := ((((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))).trans
    (u₄.rest (by decide))).trans (u₅.rest (by decide))
  have mt : t.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r6 : t.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    simp only [u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  have r3 : t.gpr .r3 = 1 := by simp only [u₅.get, u₄.get, u₃.get, u₂.get, reduceCtorEq, ↓reduceIte]
  have p10 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 a := by
    simp only [u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  have p1 : t.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 b := by
    simp only [u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  have p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * k) := by
    simp only [u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  clear u₁ u₂ u₃ u₄ u₅
  refine WP.seq (ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 a) (step := 4) (k := k)
    (fun j u => Rest ltClob s u ∧ u.mem = s.mem ∧ u.gpr .r6 = VG.Proof.X25519.Arm.mask16 ∧
      u.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 b + BitVec.ofNat 32 (4 * j) ∧ (u.gpr .r3).toNat ≤ 1 ∧
      Chain s.mem base a b j (u.gpr .r3).toNat)
    (by decide) hk (by omega_arith) (fun j u u' ⟨c1, c2, c3, c4, c5, c6⟩ F => ⟨c1.trans (F.rest _),
      by rw [F.mem]; exact c2, by rw [F.gpr]; exact c3, by rw [F.gpr]; exact c4, by rw [F.gpr]; exact c5,
      by rw [F.gpr]; exact c6⟩)
    ⟨R, mt, r6, by rw [p1]; exact (BitVec.add_zero _).symm, by rw [r3]; decide, 0, by decide,
      by simp only [r3, val32]; rfl⟩
    p10 (by rw [p9, Offset.add_add]) ?_ fun u ⟨Ru, Mu, _, _, Cu, T, hT, V⟩ _ => ?_)
  · intro j hj u ⟨Ru, Mu, r6u, p1u, Cu, T, hT, V⟩ pu p9u
    have wu := hs.of_rest Ru (by decide)
    have e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
    simp only [List.cons_append, List.append_assoc, List.nil_append]
    refine wp_ldr (by decide) (wu.ea (K := a + 4 * j) (at_ptr pu e12) (by omega_arith))
      (wu.read (d := a + 4 * j + 0) (n := 4) (by omega_arith)) fun u₁ v₁ => ?_
    have w₁ := wu.of_upd v₁ (by decide)
    refine wp_ldr (by decide) (w₁.ea (K := b + 4 * j) (at_ptr (by rw [v₁.other .r1 (by decide)]; exact p1u)
      (by rw [v₁.other .r12 (by decide)]; exact e12)) (by omega_arith))
      (w₁.read (d := b + 4 * j + 0) (n := 4) (by omega_arith)) fun u₂ v₂ => ?_
    have r7v : (u₂.gpr .r7).toNat = w32 s.mem base (a + 4 * j) := by
      rw [v₂.other .r7 (by decide), v₁.gpr, Mu, Nat.add_zero]
    have r5v : (u₂.gpr .r5).toNat = w32 s.mem base (b + 4 * j) := by rw [v₂.gpr, v₁.mem, Mu, Nat.add_zero]
    have c₂ : u₂.gpr .r3 = u.gpr .r3 := by rw [v₂.other .r3 (by decide), v₁.other .r3 (by decide)]
    have r6₂ : u₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
      rw [v₂.other .r6 (by decide), v₁.other .r6 (by decide)]; exact r6u
    refine borrowDigit_ok (h := 0) (by decide) r6₂ (by rw [c₂]; exact Cu) fun u₃ X₃ C₃ R₃ M₃ => ?_
    have r6₃ : u₃.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [R₃.gpr _ (by decide)]; exact r6₂
    have b₃ : (u₃.gpr .r3).toNat ≤ 1 := by
      have := hdig_lt (u₂.gpr .r7).toNat 0
      rw [C₃, X₃, c₂]; omega_arith
    refine borrowDigit_ok (h := 1) (by decide) r6₃ b₃ fun u₄ X₄ C₄ R₄ M₄ => ?_
    refine wp_bump (by decide) fun u₅ v₅ => wp_bump (by decide) fun u₆ v₆ => WP.block_nil ?_
    rw [R₃.gpr .r7 (by decide), R₃.gpr .r5 (by decide), r7v, r5v] at X₄
    rw [c₂] at X₃
    obtain ⟨hw, hc'⟩ := borrowWord (u := u₂) r7v r5v (by rw [c₂]; exact Cu) (by rw [c₂]; exact X₃) C₃ X₄ C₄
      (BitVec.isLt _) (BitVec.isLt _)
    rw [c₂] at hw
    obtain ⟨hlt, heq⟩ := chain_next hT (by omega_arith) V hw
    have c₆ : u₆.gpr .r3 = u₄.gpr .r3 := by rw [v₆.other .r3 (by decide), v₅.other .r3 (by decide)]
    refine ⟨⟨((Ru.trans (((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans
      ((R₃.mono (by decide)).trans (R₄.mono (by decide))))).trans (v₅.rest (by decide))).trans (v₆.rest (by decide)),
      by rw [v₆.mem, v₅.mem, M₄, M₃, v₂.mem, v₁.mem, Mu],
      by rw [v₆.other .r6 (by decide), v₅.other .r6 (by decide), R₄.gpr .r6 (by decide)]; exact r6₃,
      by rw [v₆.gpr, v₅.other .r1 (by decide), R₄.gpr .r1 (by decide), R₃.gpr .r1 (by decide),
        v₂.other .r1 (by decide), v₁.other .r1 (by decide)]; exact ptr_step p1u,
      by rw [c₆]; exact hc', _, by rw [pow32_succ]; exact hlt, ?_⟩,
      by rw [v₆.other .r10 (by decide), v₅.gpr, R₄.gpr .r10 (by decide), R₃.gpr .r10 (by decide),
        v₂.other .r10 (by decide), v₁.other .r10 (by decide)]; exact ptr_step pu,
      by rw [v₆.other .r9 (by decide), v₅.other .r9 (by decide), R₄.gpr .r9 (by decide), R₃.gpr .r9 (by decide),
        v₂.other .r9 (by decide), v₁.other .r9 (by decide)]; exact p9u⟩
    rw [c₆, pow32_succ, val32_succ, val32_succ]
    exact heq
  · refine wp_dp (op2_imm (by decide)) fun t v => WP.block_nil ⟨?_, Ru.trans (v.rest (by decide)), by rw [v.mem, Mu]⟩
    have hc := chain_carry hT Cu V
    have e3 : u.gpr .r3 = if val32 s.mem base a k < val32 s.mem base b k then 0 else 1 := by
      apply BitVec.eq_of_toNat_eq; rw [hc]; split <;> rfl
    rw [v.gpr, dpVal, e3]
    by_cases h : val32 s.mem base a k < val32 s.mem base b k <;> simp only [h, ↓reduceIte, mask32] <;> decide

/-- `[o] = [a] - [b]` modulo `2^(32k)`. -/
theorem subWords_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k o a b : Nat} (hk : 0 < k)
    (ha : a + 4 * k ≤ size) (hb : b + 4 * k ≤ size) (ho : o + 4 * k ≤ size) (h16a : a + 4 * k < 2 ^ 16)
    (h16b : b < 2 ^ 16) (h16o : o < 2 ^ 16) (hsa : o + 4 * k ≤ a ∨ a + 4 * k ≤ o)
    (hsb : o + 4 * k ≤ b ∨ b + 4 * k ≤ o) :
    WP isa (subWords k o a b) s fun t =>
      val32 t.mem base o k = (val32 s.mem base a k + 2 ^ (32 * k) - val32 s.mem base b k) % 2 ^ (32 * k) ∧
      Rest dclob s t ∧ Outside base o (4 * k) s.mem t.mem := by
  have hn := hs.nowrap
  unfold subWords
  refine WP.seq (wp_movw fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_ptr (d := .r10) (by decide) (by omega_arith) fun s₃ u₃ => wp_ptr (d := .r1) (by decide) (by omega_arith) fun s₄ u₄ =>
    wp_ptr (d := .r8) (by decide) (by omega_arith) fun s₅ u₅ =>
    wp_ptr (d := .r9) (by decide) (by omega_arith) fun t u₆ => WP.block_nil ?_)
  have R : Rest dclob s t := (((((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))).trans
    (u₄.rest (by decide))).trans (u₅.rest (by decide))).trans (u₆.rest (by decide))
  have mt : t.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r6 : t.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  have r3 : t.gpr .r3 = 1 := by simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, reduceCtorEq, ↓reduceIte]
  have p10 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 a := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  have p1 : t.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 b := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  have p8 : t.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 o := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  have p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * k) := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  clear u₁ u₂ u₃ u₄ u₅ u₆
  refine ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 a) (step := 4) (k := k)
    (fun j u => Rest dclob s u ∧ Outside base o (4 * k) s.mem u.mem ∧ u.gpr .r6 = VG.Proof.X25519.Arm.mask16 ∧
      u.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 b + BitVec.ofNat 32 (4 * j) ∧
      u.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 o + BitVec.ofNat 32 (4 * j) ∧ (u.gpr .r3).toNat ≤ 1 ∧
      val32 u.mem base o j + 2 ^ (32 * j) * (u.gpr .r3).toNat + val32 s.mem base b j =
        val32 s.mem base a j + 2 ^ (32 * j))
    (by decide) hk (by omega_arith) (fun j u u' ⟨c1, c2, c3, c4, c5, c6, c7⟩ F => ⟨c1.trans (F.rest _),
      by rw [F.mem]; exact c2, by rw [F.gpr]; exact c3, by rw [F.gpr]; exact c4, by rw [F.gpr]; exact c5,
      by rw [F.gpr]; exact c6, by rw [F.gpr, F.mem]; exact c7⟩)
    ⟨R, by rw [mt]; exact Outside.refl _ _ _ _, r6, by rw [p1]; exact (BitVec.add_zero _).symm,
      by rw [p8]; exact (BitVec.add_zero _).symm, by rw [r3]; decide, by simp only [r3, val32]; rfl⟩
    p10 (by rw [p9, Offset.add_add]) ?_ fun u ⟨Ru, Ou, _, _, _, Cu, V⟩ _ =>
      ⟨chain_low (val32_lt _ _ _ _) Cu V, Ru, Ou⟩
  intro j hj u ⟨Ru, Ou, r6u, p1u, p8u, Cu, V⟩ pu p9u
  have wu := hs.of_rest Ru (by decide)
  have e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  refine wp_ldr (by decide) (wu.ea (K := a + 4 * j) (at_ptr pu e12) (by omega_arith))
    (wu.read (d := a + 4 * j + 0) (n := 4) (by omega_arith)) fun u₁ v₁ => ?_
  have w₁ := wu.of_upd v₁ (by decide)
  refine wp_ldr (by decide) (w₁.ea (K := b + 4 * j) (at_ptr (by rw [v₁.other .r1 (by decide)]; exact p1u)
    (by rw [v₁.other .r12 (by decide)]; exact e12)) (by omega_arith))
    (w₁.read (d := b + 4 * j + 0) (n := 4) (by omega_arith)) fun u₂ v₂ => ?_
  have r7v : (u₂.gpr .r7).toNat = w32 s.mem base (a + 4 * j) := by
    rw [v₂.other .r7 (by decide), v₁.gpr, Nat.add_zero]; exact Ou.w32 (by omega_arith) (by omega_arith)
  have r5v : (u₂.gpr .r5).toNat = w32 s.mem base (b + 4 * j) := by
    rw [v₂.gpr, v₁.mem, Nat.add_zero]; exact Ou.w32 (by omega_arith) (by omega_arith)
  have c₂ : u₂.gpr .r3 = u.gpr .r3 := by rw [v₂.other .r3 (by decide), v₁.other .r3 (by decide)]
  have r6₂ : u₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [v₂.other .r6 (by decide), v₁.other .r6 (by decide)]; exact r6u
  refine borrowDigit_ok (h := 0) (by decide) r6₂ (by rw [c₂]; exact Cu) fun u₃ X₃ C₃ R₃ M₃ => ?_
  have r6₃ : u₃.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [R₃.gpr _ (by decide)]; exact r6₂
  refine wp_dp (op2_reg _ _) fun u₃' v₃ => ?_
  have b₃ : (u₃'.gpr .r3).toNat ≤ 1 := by
    have := hdig_lt (u₂.gpr .r7).toNat 0
    rw [v₃.other .r3 (by decide), C₃, X₃, c₂]; omega_arith
  refine borrowDigit_ok (h := 1) (by decide) (by rw [v₃.other .r6 (by decide)]; exact r6₃) b₃
    fun u₄ X₄ C₄ R₄ M₄ => ?_
  refine wp_dp (op2_lsl (by decide)) fun u₅ v₅ => ?_
  have w₅ : Ws u₅ base size := ((((w₁.of_upd v₂ (by decide)).of_rest R₃ (by decide)).of_upd v₃ (by decide)).of_rest
    R₄ (by decide)).of_upd v₅ (by decide)
  have e8 : u₅.gpr .r8 = u₅.gpr .r12 + BitVec.ofNat 32 (o + 4 * j) := by
    rw [v₅.other .r8 (by decide), v₅.other .r12 (by decide), R₄.gpr .r8 (by decide), R₄.gpr .r12 (by decide),
      v₃.other .r8 (by decide), v₃.other .r12 (by decide), R₃.gpr .r8 (by decide), R₃.gpr .r12 (by decide),
      v₂.other .r8 (by decide), v₂.other .r12 (by decide), v₁.other .r8 (by decide), v₁.other .r12 (by decide)]
    exact at_ptr p8u e12
  refine wp_str (by decide) (w₅.ea (d := 0) e8 (by omega_arith)) (w₅.write (d := o + 4 * j + 0) (n := 4) (by omega_arith))
    fun u₆ m₆ => wp_bump (by decide) fun u₇ v₇ => wp_bump (by decide) fun u₈ v₈ => wp_bump (by decide) fun u₉ v₉ =>
      WP.block_nil ?_
  rw [v₃.other .r7 (by decide), v₃.other .r5 (by decide), R₃.gpr .r7 (by decide), R₃.gpr .r5 (by decide), r7v, r5v,
    v₃.other .r3 (by decide)] at X₄
  rw [c₂] at X₃
  obtain ⟨hw, hc'⟩ := borrowWord (u := u₂) r7v r5v (by rw [c₂]; exact Cu) (by rw [c₂]; exact X₃) C₃ X₄ C₄
    (BitVec.isLt _) (BitVec.isLt _)
  rw [c₂] at hw
  -- The packed word.
  have r2₄ : (u₄.gpr .r2).toNat = (u₃.gpr .r4).toNat % 2 ^ 16 := by
    rw [R₄.gpr .r2 (by decide), v₃.gpr, dpVal, toNat_and_r6 r6₃]
  have pk : (u₅.gpr .r2).toNat = (u₃.gpr .r4).toNat % 2 ^ 16 + (u₄.gpr .r4).toNat % 2 ^ 16 * 2 ^ 16 := by
    rw [v₅.gpr, dpVal, pack_toNat _ _ (by rw [r2₄]; omega_arith), r2₄]
  rw [← pk] at hw
  have hnw : base.toNat + (o + 4 * j) + 4 ≤ 2 ^ 32 := by omega_arith
  have m₉ : u₉.mem = u.mem.writeW (off base (o + 4 * j)) (u₅.gpr .r2) := by
    rw [v₉.mem, v₈.mem, v₇.mem, m₆.mem, v₅.mem, M₄, v₃.mem, M₃, v₂.mem, v₁.mem, Nat.add_zero]
  have Vo : val32 u₉.mem base o j = val32 u.mem base o j := by
    rw [m₉]; exact val32_congr fun i hi => w32_write_lt hnw (by omega_arith) _
  have Wo : w32 u₉.mem base (o + 4 * j) = (u₅.gpr .r2).toNat := by rw [m₉, w32_write_self]
  obtain ⟨_, heq⟩ := chain_next (val32_lt u.mem base o j) (BitVec.isLt _) V hw
  have c₉ : u₉.gpr .r3 = u₄.gpr .r3 := by
    rw [v₉.other .r3 (by decide), v₈.other .r3 (by decide), v₇.other .r3 (by decide), m₆.gpr, v₅.other .r3 (by decide)]
  refine ⟨⟨(((((Ru.trans (((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans
    ((R₃.mono (by decide)).trans (v₃.rest (by decide))))).trans ((R₄.mono (by decide)).trans (v₅.rest (by decide)))).trans
    (m₆.rest _)).trans (v₇.rest (by decide))).trans (v₈.rest (by decide))).trans (v₉.rest (by decide)),
    by rw [m₉]; exact Ou.write32 (by omega_arith) (by omega_arith) (by omega_arith) _, ?_, ?_, ?_, by rw [c₉]; exact hc', ?_⟩, ?_, ?_⟩
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, reduceCtorEq, ↓reduceIte]
    rw [R₄.gpr .r6 (by decide), v₃.other .r6 (by decide)]; exact r6₃
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, reduceCtorEq, ↓reduceIte]
    rw [R₄.gpr .r1 (by decide), v₃.other .r1 (by decide), R₃.gpr .r1 (by decide), v₂.other .r1 (by decide),
      v₁.other .r1 (by decide)]; exact ptr_step p1u
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, reduceCtorEq, ↓reduceIte]
    rw [R₄.gpr .r8 (by decide), v₃.other .r8 (by decide), R₃.gpr .r8 (by decide), v₂.other .r8 (by decide),
      v₁.other .r8 (by decide)]; exact ptr_step p8u
  · rw [c₉, pow32_succ, val32_succ, val32_succ, val32_succ, Vo, Wo]
    exact heq
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, reduceCtorEq, ↓reduceIte]
    rw [R₄.gpr .r10 (by decide), v₃.other .r10 (by decide), R₃.gpr .r10 (by decide), v₂.other .r10 (by decide),
      v₁.other .r10 (by decide)]; exact ptr_step pu
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, reduceCtorEq, ↓reduceIte]
    rw [R₄.gpr .r9 (by decide), v₃.other .r9 (by decide), R₃.gpr .r9 (by decide), v₂.other .r9 (by decide),
      v₁.other .r9 (by decide)]; exact p9u

/-! ## Nonzero and equality -/

theorem val32_succ_eq_zero (m : Mem) (base : Addr) (a j : Nat) :
    val32 m base a (j + 1) = 0 ↔ val32 m base a j = 0 ∧ w32 m base (a + 4 * j) = 0 := by
  have : (2 : Nat) ^ (32 * j) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)
  rw [val32_succ, Nat.add_eq_zero_iff, Nat.mul_eq_zero]
  simp only [this, false_or]

/-- `r2` is all ones iff `[a] ≠ 0`. -/
theorem nonzero_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k a : Nat} (hk : 0 < k)
    (ha : a + 4 * k ≤ size) (h16a : a + 4 * k < 2 ^ 16) :
    WP isa (nonzero k a) s fun t =>
      t.gpr .r2 = mask32 (val32 s.mem base a k ≠ 0) ∧ Rest ltClob s t ∧ t.mem = s.mem := by
  have hn := hs.nowrap
  unfold nonzero
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ =>
    wp_ptr (d := .r10) (by decide) (by omega_arith) fun s₂ u₂ =>
    wp_ptr (d := .r9) (by decide) (by omega_arith) fun t u₃ => WP.block_nil ?_)
  have R : Rest ltClob s t := ((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))
  have mt : t.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have r3 : t.gpr .r3 = 0 := by simp only [u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  have p10 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 a := by
    simp only [u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  have p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * k) := by
    simp only [u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  clear u₁ u₂ u₃
  refine WP.seq (ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 a) (step := 4) (k := k)
    (fun j u => Rest ltClob s u ∧ u.mem = s.mem ∧ (u.gpr .r3 = 0 ↔ val32 s.mem base a j = 0))
    (by decide) hk (by omega_arith) (fun j u u' ⟨c1, c2, c3⟩ F => ⟨c1.trans (F.rest _),
      by rw [F.mem]; exact c2, by rw [F.gpr]; exact c3⟩)
    ⟨R, mt, by rw [r3]; exact ⟨fun _ => rfl, fun _ => rfl⟩⟩
    p10 (by rw [p9, Offset.add_add]) ?_ fun u ⟨Ru, Mu, Zu⟩ _ => ?_)
  · intro j hj u ⟨Ru, Mu, Zu⟩ pu p9u
    have wu := hs.of_rest Ru (by decide)
    have e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
    refine wp_ldr (by decide) (wu.ea (K := a + 4 * j) (at_ptr pu e12) (by omega_arith))
      (wu.read (d := a + 4 * j + 0) (n := 4) (by omega_arith)) fun u₁ v₁ => ?_
    refine wp_dp (op2_reg _ _) fun u₂ v₂ => wp_bump (by decide) fun u₃ v₃ => WP.block_nil
      ⟨⟨((Ru.trans (v₁.rest (by decide))).trans (v₂.rest (by decide))).trans (v₃.rest (by decide)),
        by rw [v₃.mem, v₂.mem, v₁.mem, Mu], ?_⟩, ?_, ?_⟩
    · have hor : ∀ x y : BitVec 32, x ||| y = 0 ↔ x = 0 ∧ y = 0 := fun _ _ => BitVec.or_eq_zero_iff
      rw [v₃.other .r3 (by decide), v₂.gpr, dpVal, hor, v₁.other .r3 (by decide), Zu, v₁.gpr, Mu,
        Nat.add_zero, w32_eq_zero_iff, val32_succ_eq_zero]
    · rw [v₃.gpr, v₂.other .r10 (by decide), v₁.other .r10 (by decide)]; exact ptr_step pu
    · rw [v₃.other .r9 (by decide), v₂.other .r9 (by decide), v₁.other .r9 (by decide)]; exact p9u
  · refine wp_mov (op2_imm (by decide)) fun s₃ u₃ => ?_
    refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
    refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
    refine wp_mov (op2_lsr (by decide)) fun s₆ u₆ => ?_
    refine wp_mov (op2_imm (by decide)) fun s₇ u₇ => ?_
    refine wp_dp (op2_reg _ _) fun s₈ u₈ => WP.block_nil ⟨?_, ?_, ?_⟩
    · have r3₅ : s₅.gpr .r3 = u.gpr .r3 := by
        rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
      have r4₆ : s₆.gpr .r4 = if u.gpr .r3 = 0 then 0 else 1 := by
        rw [u₆.gpr, u₅.gpr, dpVal, u₄.gpr, dpVal, u₃.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
          ← r3₅, negOr_shr, r3₅]
      rw [u₈.gpr, dpVal, u₇.gpr, u₇.other _ (by decide), r4₆]
      have : (if u.gpr .r3 = 0 then (0 : BitVec 32) else 1) = if decide (u.gpr .r3 ≠ 0) then 1 else 0 := by
        by_cases h : u.gpr .r3 = 0 <;> simp [h]
      rw [this, neg_bit32]
      simp only [mask32, decide_eq_true_eq, ne_eq, Zu]
    · exact Ru.trans ((u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans
        ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans (u₈.rest (by decide)))))))
    · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, Mu]

theorem mask_not (p : Prop) [Decidable p] : mask32 p ^^^ BitVec.allOnes 32 = mask32 (¬ p) := by
  by_cases hp : p <;> simp only [mask32, hp, not_true_eq_false, not_false_eq_true, ite_true, ite_false] <;> decide

/-- `allOnes` then `eor r2 r2 r4` negates the mask in `r2`. -/
theorem wp_not {s : State} {is : List Instr} {Q : State → Prop} {p : Prop} [Decidable p]
    (h2 : s.gpr .r2 = mask32 p)
    (k : ∀ t, t.gpr .r2 = mask32 (¬ p) → Rest [.r2, .r4] s t → t.mem = s.mem → WP isa (.block is) t Q) :
    WP isa (.block (allOnes ++ .dp .eor .r2 .r2 (.reg .r4) :: is)) s Q := by
  simp only [allOnes, List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_dp (op2_imm (by decide)) fun s₂ u₂ =>
    wp_dp (op2_reg _ _) fun t u₃ => k t ?_ (((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans
      (u₃.rest (by decide))) (by rw [u₃.mem, u₂.mem, u₁.mem])
  rw [u₃.gpr, dpVal, u₂.gpr, u₂.other .r2 (by decide), u₁.gpr, u₁.other .r2 (by decide), dpVal, h2, ← mask_not]
  rfl

/-- `r2` is all ones iff `[a] = [b]`. -/
theorem equal_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k a b : Nat} (hk : 0 < k)
    (ha : a + 4 * k ≤ size) (hb : b + 4 * k ≤ size) (h16a : a + 4 * k < 2 ^ 16) (h16b : b + 4 * k < 2 ^ 16) :
    WP isa (equal k a b) s fun t =>
      t.gpr .r2 = mask32 (val32 s.mem base a k = val32 s.mem base b k) ∧ Rest dclob s t ∧ t.mem = s.mem := by
  unfold equal
  refine WP.seq (WP.mono (lessThan_ok hs hk ha hb h16a (by omega_arith)) fun u ⟨eu, Ru, mu⟩ => ?_)
  refine WP.seq (wp_mov (op2_reg _ _) fun v uv => WP.block_nil ?_)
  have Rv : Rest dclob s v := (Ru.mono (by decide)).trans (uv.rest (by decide))
  refine WP.seq (WP.mono (lessThan_ok (hs.of_rest Rv (by decide)) hk hb ha h16b (by omega_arith))
    fun w ⟨ew, Rw, mw⟩ => ?_)
  refine wp_dp (op2_reg _ _) fun x ux => ?_
  have vm : v.mem = s.mem := by rw [uv.mem, mu]
  rw [vm] at ew
  have r8w : w.gpr .r8 = mask32 (val32 s.mem base a k < val32 s.mem base b k) := by
    rw [Rw.gpr .r8 (by decide), uv.gpr, eu]
  have hx : x.gpr .r2 = mask32 ¬(val32 s.mem base a k = val32 s.mem base b k) := by
    rw [ux.gpr, dpVal, ew, r8w]
    generalize val32 s.mem base a k = A
    generalize val32 s.mem base b k = B
    rcases Nat.lt_trichotomy A B with h | rfl | h
    · simp only [mask32, h, Nat.lt_asymm h, Nat.ne_of_lt h, ↓reduceIte, not_false_eq_true]; decide
    · simp only [mask32, Nat.lt_irrefl, ↓reduceIte, not_true_eq_false]; decide
    · simp only [mask32, h, Nat.lt_asymm h, Nat.ne_of_gt h, ↓reduceIte, not_false_eq_true]; decide
  refine wp_not hx fun t e Rt mt => WP.block_nil ⟨?_, ((((Ru.mono (by decide)).trans (uv.rest (by decide))).trans
    (Rw.mono (by decide))).trans (ux.rest (by decide))).trans (Rt.mono (by decide)), by rw [mt, ux.mem, mw, vm]⟩
  rw [e]
  by_cases h : val32 s.mem base a k = val32 s.mem base b k <;> simp only [mask32, h, ↓reduceIte, not_true_eq_false,
    not_false_eq_true]

/-! ## The flag -/

/-- The flag word at `flag`. -/
abbrev flagW (base : Addr) (flag : Nat) (s : State) : BitVec 32 := s.mem.readW (off base flag) 32

/-- `[flag] &= r2`, through `r4`. -/
theorem andFlag_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {flag : Nat}
    (hf : flag + 4 ≤ size) (hf4 : flag < 4096) :
    WP isa (.block (andFlag flag)) s fun t =>
      flagW base flag t = flagW base flag s &&& s.gpr .r2 ∧ Rest [.r4] s t ∧ Outside base flag 4 s.mem t.mem := by
  have hn := hs.nowrap
  simp only [andFlag]
  refine wp_ldr hf4 (hs.ea12 (by omega_arith)) (hs.read hf) fun s₁ u₁ => wp_dp (op2_reg _ _) fun s₂ u₂ => ?_
  have k₂ : Rest [.r4] s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
  have hs₂ := hs.of_rest k₂ (by decide)
  refine wp_str hf4 (hs₂.ea12 (by omega_arith)) (hs₂.write hf) fun s₃ m₃ => WP.block_nil ⟨?_, k₂.trans (m₃.rest _), ?_⟩
  · rw [flagW, flagW, m₃.mem, Mem.readW_writeW_self32, u₂.gpr, dpVal, u₁.gpr, u₁.other _ (by decide)]
  · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega_arith)

theorem mask32_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : mask32 p = mask32 q := by
  by_cases hp : p
  · simp only [mask32, hp, h.mp hp, ↓reduceIte]
  · simp only [mask32, hp, mt h.mpr hp, ↓reduceIte]

/-- The flag `&=` the mask of `0 < [a] < [m]`. -/
theorem checkRange_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k a m flag : Nat} (hk : 0 < k)
    (ha : a + 4 * k ≤ size) (hm : m + 4 * k ≤ size) (h16a : a + 4 * k < 2 ^ 16) (h16m : m < 2 ^ 16)
    (hf : flag + 4 ≤ size) (hf4 : flag < 4096) :
    WP isa (checkRange k a m flag) s fun t =>
      flagW base flag t = flagW base flag s &&&
        mask32 (0 < val32 s.mem base a k ∧ val32 s.mem base a k < val32 s.mem base m k) ∧
      Rest dclob s t ∧ Outside base flag 4 s.mem t.mem := by
  unfold checkRange
  refine WP.seq (WP.mono (lessThan_ok hs hk ha hm h16a h16m) fun u ⟨eu, Ru, mu⟩ => ?_)
  refine WP.seq (wp_mov (op2_reg _ _) fun v uv => WP.block_nil ?_)
  have Rv : Rest dclob s v := (Ru.mono (by decide)).trans (uv.rest (by decide))
  refine WP.seq (WP.mono (nonzero_ok (hs.of_rest Rv (by decide)) hk ha h16a) fun w ⟨ew, Rw, mw⟩ => ?_)
  refine wp_dp (op2_reg _ _) fun x ux => ?_
  have Rx : Rest dclob s x := (Rv.trans (Rw.mono (by decide))).trans (ux.rest (by decide))
  have mx : x.mem = s.mem := by rw [ux.mem, mw, uv.mem, mu]
  refine WP.mono (andFlag_ok (hs.of_rest Rx (by decide)) hf hf4) fun t ⟨et, Rt, Ot⟩ =>
    ⟨?_, Rx.trans (Rt.mono (by decide)), by rw [← mx]; exact Ot⟩
  rw [et, flagW, flagW, mx, ux.gpr, dpVal, ew, Rw.gpr .r8 (by decide), uv.gpr, eu, uv.mem, mu, mask32_and]
  exact congrArg _ (mask32_iff (by rw [Nat.pos_iff_ne_zero]))

/-- The flag `&=` the mask of `[a] ≠ 0` (`wantNonzero`) or of `[a] = 0`. -/
theorem checkZero_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k a flag : Nat} (hk : 0 < k)
    (ha : a + 4 * k ≤ size) (h16a : a + 4 * k < 2 ^ 16) (hf : flag + 4 ≤ size) (hf4 : flag < 4096)
    (wantNonzero : Bool) :
    WP isa (checkZero k a flag wantNonzero) s fun t =>
      flagW base flag t = flagW base flag s &&&
        mask32 (if wantNonzero then val32 s.mem base a k ≠ 0 else val32 s.mem base a k = 0) ∧
      Rest dclob s t ∧ Outside base flag 4 s.mem t.mem := by
  unfold checkZero
  refine WP.seq (WP.mono (nonzero_ok hs hk ha h16a) fun u ⟨eu, Ru, mu⟩ => ?_)
  have wu := hs.of_rest Ru (by decide)
  cases wantNonzero
  · simp only [Bool.false_eq_true, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append]
    refine wp_not eu fun v ev Rv mv => WP.mono (andFlag_ok (wu.of_rest Rv (by decide)) hf hf4) fun t ⟨et, Rt, Ot⟩ =>
      ⟨?_, ((Ru.mono (by decide)).trans (Rv.mono (by decide))).trans (Rt.mono (by decide)),
        by rw [← mu, ← mv]; exact Ot⟩
    rw [et, flagW, flagW, mv, mu, ev]
    exact congrArg _ (mask32_iff Classical.not_not)
  · simp only [↓reduceIte, List.nil_append]
    refine WP.mono (andFlag_ok wu hf hf4) fun t ⟨et, Rt, Ot⟩ =>
      ⟨?_, (Ru.mono (by decide)).trans (Rt.mono (by decide)), by rw [← mu]; exact Ot⟩
    rw [et, flagW, flagW, mu, eu]

/-! ## Constants -/

theorem wp_movt {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons rfl (k _ (VG.Proof.X25519.Arm.Upd.setReg _ _ _))

/-- `movImm x` builds `x`'s low word. -/
theorem movImm_val (x : Nat) :
    (BitVec.ofNat 16 (x >>> 16) ++ ((BitVec.ofNat 16 x).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _)]
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  omega_arith

/-- A number from its words. -/
theorem val32_of_words {m : Mem} {base : Addr} {o x : Nat} :
    ∀ {k}, (∀ i < k, w32 m base (o + 4 * i) = x >>> (32 * i) % 2 ^ 32) → val32 m base o k = x % 2 ^ (32 * k)
  | 0, _ => by simp only [val32, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | k + 1, h => by
    rw [val32_succ, val32_of_words fun i hi => h i (by omega_arith), h k (by omega_arith), Nat.shiftRight_eq_div_pow,
      show 32 * (k + 1) = 32 * k + 32 by omega_arith, Nat.pow_add, Nat.mod_mul]

/-- The nonzero words of a constant, stored at `[r10 + 4i]`. -/
theorem constWords_ok {u : State} {base : Addr} {size : Nat} (hs : Ws u base size) {k o x : Nat}
    (h10 : u.gpr .r10 = u.gpr .r12 + BitVec.ofNat 32 o) (ho : o + 4 * k ≤ size) (hk4 : 4 * k ≤ 4096)
    (hz : ∀ i < k, w32 u.mem base (o + 4 * i) = 0) :
    ∀ j ≤ k, WP isa (.block ((List.range j).flatMap fun i =>
        if x >>> (32 * i) % 2 ^ 32 = 0 then [] else movImm (x >>> (32 * i)) ++
          ([.str .r4 .r10 (4 * i)] : List Instr))) u fun t =>
      Rest [.r4] u t ∧ (∀ i < k, w32 t.mem base (o + 4 * i) = if i < j then x >>> (32 * i) % 2 ^ 32 else 0) ∧
      Outside base o (4 * k) u.mem t.mem
  | 0, _ => WP.block_nil ⟨Rest.refl _ _, fun i hi => by rw [hz i hi]; rfl, Outside.refl _ _ _ _⟩
  | j + 1, hj => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine VG.Proof.X25519.Arm.WP.append (constWords_ok hs h10 ho hk4 hz j (by omega_arith)) fun t ⟨R, V, O⟩ => ?_
    by_cases hx : x >>> (32 * j) % 2 ^ 32 = 0
    · rw [ite_eq_left hx]
      refine WP.block_nil ⟨R, fun i hi => ?_, O⟩
      rw [V i hi]
      rcases Nat.lt_trichotomy i j with h | rfl | h
      · rw [ite_eq_left h, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right (Nat.lt_irrefl _), ite_eq_left (Nat.lt_succ_self _), hx]
      · rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
    · rw [ite_eq_right hx]
      have wt := hs.of_rest R (by decide)
      have e10 : t.gpr .r10 = t.gpr .r12 + BitVec.ofNat 32 o := by
        rw [R.gpr .r10 (by decide), R.gpr .r12 (by decide)]; exact h10
      simp only [movImm, List.cons_append, List.nil_append]
      refine wp_movw fun t₁ v₁ => wp_movt fun t₂ v₂ => ?_
      have w₂ := (wt.of_upd v₁ (by decide)).of_upd v₂ (by decide)
      refine wp_str (by omega_arith) (w₂.ea (K := o) (d := 4 * j)
        (by rw [v₂.other .r10 (by decide), v₁.other .r10 (by decide), v₂.other .r12 (by decide),
          v₁.other .r12 (by decide)]; exact e10) (by omega_arith))
        (w₂.write (d := o + 4 * j) (n := 4) (by omega_arith)) fun t₃ m₃ => WP.block_nil ⟨?_, fun i hi => ?_, ?_⟩
      · exact ((R.trans (v₁.rest (by decide))).trans (v₂.rest (by decide))).trans (m₃.rest _)
      · have hv : t₂.gpr .r4 = BitVec.ofNat 32 (x >>> (32 * j)) := by rw [v₂.gpr, v₁.gpr, movImm_val]
        rw [m₃.mem, v₂.mem, v₁.mem, hv]
        rcases Nat.lt_trichotomy i j with h | rfl | h
        · rw [w32_write_lt (by omega_arith) (by omega_arith), V i hi, ite_eq_left h, ite_eq_left (by omega_arith)]
        · rw [w32_write_self, BitVec.toNat_ofNat, ite_eq_left (Nat.lt_succ_self _)]
        · rw [w32_write_ne (size := o + 4 * k) (by omega_arith) (by omega_arith) (by omega_arith) (.inr (by omega_arith)), V i hi,
            ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
      · rw [m₃.mem, v₂.mem, v₁.mem]; exact O.write32 (by omega_arith) (by omega_arith) (by omega_arith) _

/-- `[o] = x` modulo `2^(32k)`. -/
theorem setConst_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k o x : Nat} (hk : 0 < k)
    (ho : o + 4 * k ≤ size) (h16 : o + 4 * k < 2 ^ 16) (hk4 : 4 * k ≤ 4096) :
    WP isa (setConst k o x) s fun t =>
      val32 t.mem base o k = x % 2 ^ (32 * k) ∧ Rest dclob s t ∧ Outside base o (4 * k) s.mem t.mem := by
  unfold Dynamic.setConst
  refine WP.seq (WP.mono (zeros_ok hs hk ho h16) fun u ⟨wu, Z, O, R⟩ => ?_)
  refine wp_ptr (d := .r10) (by decide) (by omega_arith) fun v uv => ?_
  have wv := wu.of_upd uv (by decide)
  refine WP.mono (constWords_ok wv (k := k) (x := x)
    (by rw [uv.gpr, uv.other .r12 (by decide)]) ho hk4 (fun i hi => by rw [uv.mem]; exact Z i hi) k (Nat.le_refl _))
    fun t ⟨Rt, Vt, Ot⟩ => ⟨val32_of_words fun i hi => by rw [Vt i hi, ite_eq_left hi], ((R.mono (by decide)).trans
      (uv.rest (by decide))).trans (Rt.mono (by decide)), by rw [← uv.mem] at O; exact O.trans Ot⟩

/-- `r2` is all ones iff `[a] < x`, through `[tmp]`. -/
theorem lessThanConstant_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k a tmp x : Nat}
    (hk : 0 < k) (ha : a + 4 * k ≤ size) (ht : tmp + 4 * k ≤ size) (h16a : a + 4 * k < 2 ^ 16)
    (h16t : tmp + 4 * k < 2 ^ 16) (hk4 : 4 * k ≤ 4096) (hx : x < 2 ^ (32 * k))
    (hsep : a + 4 * k ≤ tmp ∨ tmp + 4 * k ≤ a) :
    WP isa (lessThanConstant k a tmp x) s fun t =>
      t.gpr .r2 = mask32 (val32 s.mem base a k < x) ∧ Rest dclob s t ∧ Outside base tmp (4 * k) s.mem t.mem := by
  have hn := hs.nowrap
  unfold lessThanConstant
  refine WP.seq (WP.mono (setConst_ok hs hk ht h16t hk4) fun u ⟨Vu, Ru, Ou⟩ => ?_)
  refine WP.mono (lessThan_ok (hs.of_rest Ru (by decide)) hk ha ht h16a (by omega_arith)) fun t ⟨et, Rt, mt⟩ =>
    ⟨?_, Ru.trans (Rt.mono (by decide)), by rw [mt]; exact Ou⟩
  rw [et, Vu, Nat.mod_eq_of_lt hx, Ou.val32 hsep (by omega_arith)]

/-! ## Widths -/

/-- `r2` is all ones iff `2^(bits-1) ≤ [a] < 2^bits`, for `0 < bits ≤ 64n`; `r11` changes too. -/
theorem widthMask_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {n a tmp bits : Nat}
    (hn : 0 < n) (ha : a + 8 * n ≤ size) (ht : tmp + 8 * n ≤ size) (h16a : a + 8 * n < 2 ^ 16)
    (h16t : tmp + 8 * n < 2 ^ 16) (hn4 : 8 * n ≤ 4096) (hb : 0 < bits) (hbn : bits ≤ 64 * n)
    (hsep : a + 8 * n ≤ tmp ∨ tmp + 8 * n ≤ a) :
    WP isa (widthMask n a tmp bits) s fun t =>
      t.gpr .r2 = mask32 (2 ^ (bits - 1) ≤ val32 s.mem base a (2 * n) ∧ val32 s.mem base a (2 * n) < 2 ^ bits) ∧
      Rest (.r11 :: dclob) s t ∧ Outside base tmp (8 * n) s.mem t.mem := by
  have e8 : 4 * (2 * n) = 8 * n := by omega_arith
  have e64 : 32 * (2 * n) = 64 * n := by omega_arith
  have hp1 : 2 ^ (bits - 1) < 2 ^ (32 * (2 * n)) := by
    rw [e64]; exact Nat.pow_lt_pow_right (by decide) (by omega_arith)
  unfold widthMask
  refine WP.seq (WP.mono (lessThanConstant_ok hs (k := 2 * n) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) hp1 (by omega_arith)) fun u ⟨eu, Ru, Ou⟩ => ?_)
  refine WP.seq (wp_not eu fun v ev Rv mv => wp_mov (op2_reg _ _) fun w uw => WP.block_nil ?_)
  have Rw : Rest (.r11 :: dclob) s w :=
    ((Ru.mono (by decide)).trans (Rv.mono (by decide))).trans (uw.rest (by decide))
  have mw : w.mem = u.mem := by rw [uw.mem, mv]
  have r11 : w.gpr .r11 = mask32 ¬(val32 s.mem base a (2 * n) < 2 ^ (bits - 1)) := by rw [uw.gpr, ev]
  have Ow : Outside base tmp (8 * n) s.mem w.mem := by rw [mw, ← e8]; exact Ou
  split
  · refine WP.seq (WP.mono (lessThanConstant_ok (hs.of_rest Rw (by decide)) (k := 2 * n) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by rw [e64]; exact Nat.pow_lt_pow_right (by decide) (by omega_arith))
      (by omega_arith)) fun x ⟨ex, Rx, Ox⟩ => ?_)
    refine wp_dp (op2_reg _ _) fun t ut => WP.block_nil ⟨?_, (Rw.trans (Rx.mono (by decide))).trans
      (ut.rest (by decide)), by rw [ut.mem]; exact Ow.trans (e8 ▸ Ox)⟩
    rw [ut.gpr, dpVal, ex, Rx.gpr .r11 (by decide), r11, mw, mask32_and, Ou.val32 (by omega_arith) (by omega_arith)]
    exact mask32_iff (by rw [Nat.not_lt, and_comm])
  · refine wp_mov (op2_reg _ _) fun t ut => WP.block_nil ⟨?_, Rw.trans (ut.rest (by decide)),
      by rw [ut.mem]; exact Ow⟩
    have hlt := val32_lt u.mem base a (2 * n)
    rw [ut.gpr, r11]
    rw [Ou.val32 (by omega_arith) (by omega_arith), e64] at hlt
    have : 2 ^ (64 * n) ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) (by omega_arith)
    exact mask32_iff ⟨fun h => ⟨Nat.not_lt.mp h, by omega_arith⟩, fun h => Nat.not_lt.mpr h.1⟩

/-- A width larger than the buffer cannot match. -/
theorem optionalWidth_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {n a tmp bits : Nat}
    (hn : 0 < n) (ha : a + 8 * n ≤ size) (ht : tmp + 8 * n ≤ size) (h16a : a + 8 * n < 2 ^ 16)
    (h16t : tmp + 8 * n < 2 ^ 16) (hn4 : 8 * n ≤ 4096) (hb : 0 < bits)
    (hsep : a + 8 * n ≤ tmp ∨ tmp + 8 * n ≤ a) :
    WP isa (optionalWidth n a tmp bits) s fun t =>
      t.gpr .r2 = mask32 (2 ^ (bits - 1) ≤ val32 s.mem base a (2 * n) ∧ val32 s.mem base a (2 * n) < 2 ^ bits) ∧
      Rest (.r11 :: dclob) s t ∧ Outside base tmp (8 * n) s.mem t.mem := by
  unfold optionalWidth
  split
  · exact widthMask_ok hs hn ha ht h16a h16t hn4 hb (by omega_arith) hsep
  · refine wp_mov (op2_imm (by decide)) fun t ut => WP.block_nil ⟨?_, ut.rest (by decide),
      by rw [ut.mem]; exact Outside.refl _ _ _ _⟩
    have hlt := val32_lt s.mem base a (2 * n)
    have : 2 ^ (32 * (2 * n)) ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    rw [ut.gpr]
    rw [mask32_iff (q := False) ⟨fun h => by omega_arith, False.elim⟩]
    rfl

end VG.Proof.Dsa.Arm
