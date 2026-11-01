module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Copy
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Words
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Masks of comparisons on RISC-V

The masks the check of a public point (`Impl/Ecdh/RISCV64.lean`) and the
range checks of a scalar compute, all ones if the comparison holds, else
zero (`maskOf`): `ltMask_ok` (`[a] < [m]`, the borrow out of `[a] - [m]`,
word by word with `sbb_ok`'s subtractions) and `zeroMask_ok` (`[a] = 0`, from
the words or'ed); each changes only caller-saved registers.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Proof.Mont
open VG.Proof.X25519.RISCV64 (Rest wp_and)

theorem _root_.VG.Proof.X25519.RISCV64.Rest.app {ws₁ ws₂ : List Reg} {s₁ s₂ s₃ : State} (h₁ : Rest ws₁ s₁ s₂) (h₂ : Rest ws₂ s₂ s₃) :
    Rest (ws₁ ++ ws₂) s₁ s₃ :=
  (h₁.mono fun _ h => List.mem_append_left _ h).trans (h₂.mono fun _ h => List.mem_append_right _ h)

theorem Wide.Keeps.rest {rs : List Reg} {s s' : State} (h : VG.RISCV64.Wide.Keeps rs s s') : Rest rs s s' :=
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- `[a] - [m]`, `k` words, with the borrow in `t5`: the difference `D`, and
the borrow out. -/
theorem ltWords_ok : ∀ (k : Nat) {s : State} {base : Addr} {a m : Nat}, WsReg s base → a % 8 = 0 → m % 8 = 0 →
    a + 8 * k ≤ 2048 → m + 8 * k ≤ 2048 → (s.gpr .t5).toNat ≤ 1 →
    WP isa (.block (ltWords k a m)) s fun s' =>
      Rest [.t3, .t4, .t5, .t6, .a4] s s' ∧ s'.mem = s.mem ∧ (s'.gpr .t5).toNat ≤ 1 ∧
      ∃ D, D < 2 ^ (64 * k) ∧ D + wordsVal s.mem base m k + (s.gpr .t5).toNat =
        wordsVal s.mem base a k + 2 ^ (64 * k) * (s'.gpr .t5).toNat
  | 0, s, _, _, _, _, _, _, _, _, hc => WP.block_nil ⟨Rest.refl _ _, rfl, hc, 0, by simp [wordsVal]⟩
  | k + 1, s, base, a, m, hw, ha, hm, ha', hm', hc => by
    rw [ltWords, ltWord, List.cons_append, List.cons_append]
    refine ld_ws hw (by omega) ha fun s₁ u₁ => ld_ws (hw.of_rest (u₁.rest (ws := [.t3]) (by decide))) (by omega)
      hm fun s₂ u₂ => ?_
    have r₂ : Rest [.t3, .t4] s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
    have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
    have c₂ : s₂.gpr .t5 = s.gpr .t5 := r₂.gpr _ (by decide)
    have x₂ : s₂.gpr .t3 = word s.mem base a := by rw [u₂.other _ (by decide), u₁.gpr]
    have y₂ : s₂.gpr .t4 = word s.mem base m := by rw [u₂.gpr, u₁.mem]
    refine WP.block_append (WP.mono (P256Field.sbb_ok (s := s₂) (d := .t3) (x := .t3) (y := .t4) (c := .t5)
      (u := .t6) (v := .a4)) fun s₃ ⟨h₃, k₃⟩ => ?_)
    obtain ⟨e₃, c₃⟩ := h₃ (by rw [c₂]; exact hc)
    have r₃ : Rest [.t3, .t4, .t5, .t6, .a4] s s₃ := (r₂.app (Wide.Keeps.rest k₃)).mono (by decide)
    have m₃ : s₃.mem = s.mem := by rw [k₃.2.1, m₂]
    refine WP.mono (ltWords_ok k (hw.of_rest r₃) (a := a + 8) (m := m + 8) (by omega) (by omega) (by omega)
      (by omega) c₃) fun s₄ ⟨r₄, m₄, c₄, D, hD, eD⟩ => ⟨r₃.trans r₄ |>.mono (by decide), by rw [m₄, m₃], c₄,
        (s₃.gpr .t3).toNat + 2 ^ 64 * D, ?_, ?_⟩
    · rw [pow64_succ]
      have := (s₃.gpr .t3).isLt
      have : 2 ^ 64 * D + 2 ^ 64 ≤ 2 ^ 64 * 2 ^ (64 * k) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hD
      omega
    · rw [m₃] at eD
      rw [x₂, y₂, c₂] at e₃
      simp only [wordsVal]
      rw [pow64_succ, Nat.mul_assoc]
      generalize 2 ^ (64 * k) * (s₄.gpr .t5).toNat = Z at eD ⊢
      omega

/-- The mask `a7` of `[a] < [m]`, numbers of `n ≥ 1` words. -/
theorem ltMask_ok {n : Nat} {s : State} {base : Addr} (hw : WsReg s base) {a m : Nat} (ha : a % 8 = 0)
    (hm : m % 8 = 0) (ha' : a + 8 * n ≤ 2048) (hm' : m + 8 * n ≤ 2048) :
    WP isa (.block (ltMask n a m)) s fun s' =>
      Rest [.t3, .t4, .t5, .t6, .a4, .a7] s s' ∧ s'.mem = s.mem ∧
      s'.gpr .a7 = maskOf (decide (wordsVal s.mem base a n < wordsVal s.mem base m n)) := by
  rw [ltMask, List.singleton_append]
  refine wp_li (imm := 0) (by decide) fun s₁ u₁ => ?_
  refine WP.block_append (WP.mono (ltWords_ok n (hw.of_rest (u₁.rest (ws := [.t5]) (by decide))) ha hm ha' hm'
    (by rw [u₁.gpr]; decide)) fun s₂ ⟨r₂, m₂, c₂, D, hD, eD⟩ => ?_)
  refine wp_li (imm := 0) (by decide) fun s₃ u₃ => wp_sub fun s₄ u₄ => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact ((u₁.rest (ws := [.t5]) (by decide)).app r₂ |>.app (u₃.rest (ws := [.t6]) (by decide)) |>.app
      (u₄.rest (ws := [.a7]) (by decide))).mono (by decide)
  · rw [u₄.mem, u₃.mem, m₂, u₁.mem]
  · rw [u₁.gpr, u₁.mem] at eD
    have hA := wordsVal_lt s.mem base a n
    have hM := wordsVal_lt s.mem base m n
    rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide)]
    have : (s₂.gpr .t5).toNat = 0 ∨ (s₂.gpr .t5).toNat = 1 := by omega
    rcases this with h | h
    · have hv : s₂.gpr .t5 = 0 := BitVec.eq_of_toNat_eq h
      rw [h] at eD
      have : ¬ wordsVal s.mem base a n < wordsVal s.mem base m n := by simp at eD; omega
      rw [hv, decide_eq_false this]; rfl
    · have hv : s₂.gpr .t5 = 1 := BitVec.eq_of_toNat_eq h
      rw [h] at eD
      have : wordsVal s.mem base a n < wordsVal s.mem base m n := by
        simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero, Nat.mul_one] at eD; omega
      rw [hv, decide_eq_true this]; rfl

/-- The words or'ed into `t3`. -/
theorem orWords_ok : ∀ (k : Nat) {s : State} {base : Addr} {a : Nat}, WsReg s base → a % 8 = 0 →
    a + 8 * k ≤ 2048 →
    WP isa (.block (orWords k a)) s fun s' =>
      Rest [.t3, .t4] s s' ∧ s'.mem = s.mem ∧
      (s'.gpr .t3 = 0 ↔ s.gpr .t3 = 0 ∧ wordsVal s.mem base a k = 0)
  | 0, s, _, _, _, _, _ => WP.block_nil ⟨Rest.refl _ _, rfl, by simp [wordsVal]⟩
  | k + 1, s, base, a, hw, ha, ha' => by
    rw [orWords, List.cons_append, List.cons_append, List.nil_append]
    refine ld_ws hw (by omega) ha fun s₁ u₁ => ?_
    refine wp_or fun s₂ u₂ => ?_
    have r₂ : Rest [.t3, .t4] s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
    have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
    refine WP.mono (orWords_ok k (hw.of_rest r₂) (a := a + 8) (by omega) (by omega)) fun s₃ ⟨r₃, m₃, e₃⟩ =>
      ⟨(r₂.trans r₃).mono (by decide), by rw [m₃, m₂], ?_⟩
    have hor : ∀ x y : BitVec 64, x ||| y = 0 ↔ x = 0 ∧ y = 0 := fun _ _ => BitVec.or_eq_zero_iff
    rw [e₃, u₂.gpr, u₁.other _ (by decide), u₁.gpr, m₂, hor]
    have hw0 := (word s.mem base a).isLt
    simp only [wordsVal]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, ?_⟩
      rw [h2, h3]; rfl
    · rintro ⟨h1, h2⟩
      have hw' : (word s.mem base a).toNat = 0 := by omega
      have hr : wordsVal s.mem base (a + 8) k = 0 := by omega
      exact ⟨⟨h1, BitVec.eq_of_toNat_eq hw'⟩, hr⟩

/-- `x | -x` has its top bit set iff `x ≠ 0`. -/
theorem top_or_neg (x : BitVec 64) : ((0 - x ||| x) >>> 63) + BitVec.ofInt 64 (-1) =
    if x = 0 then BitVec.allOnes 64 else 0 := by
  by_cases hx : x = 0
  · subst hx; decide
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hx)]
    have h1 : (0 - x ||| x) >>> 63 = 1 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_or, BitVec.toNat_sub]
      have hx' : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq h)
      have hxl := x.isLt
      show ((2 ^ 64 - x.toNat + 0) % 2 ^ 64 ||| x.toNat) >>> 63 = 1
      rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
      rw [Nat.shiftRight_eq_div_pow]
      have hlt : (2 ^ 64 - x.toNat ||| x.toNat) < 2 ^ 64 := Nat.or_lt_two_pow (by omega) hxl
      have hge : 2 ^ 63 ≤ (2 ^ 64 - x.toNat ||| x.toNat) := by
        by_cases h : 2 ^ 63 ≤ x.toNat
        · exact Nat.le_trans h (Nat.right_le_or)
        · exact Nat.le_trans (by omega) (Nat.left_le_or)
      omega
    rw [h1]; decide

/-- The mask `a7` of `[a] = 0`. -/
theorem zeroMask_ok {n : Nat} {s : State} {base : Addr} (hw : WsReg s base) {a : Nat} (ha : a % 8 = 0)
    (ha' : a + 8 * n ≤ 2048) :
    WP isa (.block (zeroMask n a)) s fun s' =>
      Rest [.t3, .t4, .a7] s s' ∧ s'.mem = s.mem ∧
      s'.gpr .a7 = maskOf (decide (wordsVal s.mem base a n = 0)) := by
  rw [zeroMask, List.singleton_append]
  refine wp_li (imm := 0) (by decide) fun s₁ u₁ => ?_
  refine WP.block_append (WP.mono (orWords_ok n (hw.of_rest (u₁.rest (ws := [.t3]) (by decide))) ha ha')
    fun s₂ ⟨r₂, m₂, e₂⟩ => ?_)
  refine wp_li (imm := 0) (by decide) fun s₃ u₃ => wp_sub fun s₄ u₄ => wp_or fun s₅ u₅ =>
    wp_srl (by decide) fun s₆ u₆ => WP.cons (exec_addi (by decide)) (WP.block_nil ⟨?_, ?_, ?_⟩)
  · refine ((u₁.rest (ws := [.t3]) (by decide)).app r₂ |>.app (u₃.rest (ws := [.t4]) (by decide)) |>.app
      (u₄.rest (ws := [.t4]) (by decide)) |>.app (u₅.rest (ws := [.t4]) (by decide)) |>.app
      (u₆.rest (ws := [.t4]) (by decide)) |>.app ((Upd.write s₆ .a7 _).rest (ws := [.a7]) (by decide))).mono
      (ws' := [.t3, .t4, .a7]) (by decide)
  · show s₆.mem = s.mem
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem]
  · show (s₆.write .a7 (s₆.gpr .t4 + BitVec.ofInt 64 (-1))).gpr .a7 = _
    simp only [State.write, ↓reduceIte]
    rw [u₆.gpr, u₅.gpr, u₄.gpr, u₄.other .t3 (by decide), u₃.gpr, u₃.other .t3 (by decide),
      show BitVec.ofNat 64 0 = 0 from rfl, top_or_neg]
    rw [u₁.gpr, u₁.mem, show BitVec.ofNat 64 0 = 0 from rfl] at e₂
    simp only [true_and] at e₂
    by_cases h : wordsVal s.mem base a n = 0
    · simp only [e₂.mpr h, decide_eq_true h, ↓reduceIte]; rfl
    · have : ¬ s₂.gpr .t3 = 0 := fun h' => h (e₂.mp h')
      simp only [this, decide_eq_false h, ↓reduceIte]; rfl

end VG.Proof.Weierstrass.RISCV64
