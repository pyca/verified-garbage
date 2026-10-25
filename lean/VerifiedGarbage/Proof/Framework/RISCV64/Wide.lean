module

public import VerifiedGarbage.Impl.Words.RISCV64.Wide
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RISC-V: multiword arithmetic with `sltu` carries

Untrusted: everything here is checked by Lean. The effect of the sequences
of `Impl/Words/RISCV64/Wide.lean` on the numbers their registers hold
(`toNat`), and that they change only the registers they name (`Keeps`):
* `carry`: after `d := a + b`, `sltu c, d, b` is the carry out of the sum;
* `mulWide_ok`: the 128-bit product of two words;
* `add2_ok`, `mulAdd_ok`, `mulAddSmall_ok`: sums modulo `2¹²⁸`;
* `add3_ok`, `addW3_ok`: sums modulo `2¹⁹²`.

The registers' distinctness, which the sequences need, are hypotheses that
`decide` proves for the literal registers of a caller.
-/

@[expose] public section

namespace VG.RISCV64.Wide

open VG.Impl.Words.RISCV64

/-- `s'` is `s` with only the registers `rs` changed. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
    s'.sp = s.sp

theorem Keeps.gpr' {rs : List Reg} {s s' : State} (h : Keeps rs s s') {r : Reg}
    (hr : r ∉ rs := by decide) : s'.gpr r = s.gpr r := h.1 r hr

theorem Keeps.refl (rs : List Reg) (s : State) : Keeps rs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keeps rs s₁ s₂)
    (h₂ : Keeps rs' s₂ s₃) : Keeps (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1],
   h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1,
   h₂.2.2.2.2.trans h₁.2.2.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : Keeps rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : Keeps rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

/-- A state built by writes keeps everything but the registers written. -/
theorem Keeps.write {rs : List Reg} {s s' : State} (h : Keeps rs s s') {d : Reg} (v : BitVec 64)
    (hd : d ∈ rs) : Keeps rs s (s'.write d v) :=
  ⟨fun r hr => by
    rw [RegUpd.gpr_write_of_ne _ _ (fun e => hr (by rw [e]; exact hd))]; exact h.1 r hr, h.2⟩

/-! ## Numbers -/

/-- The carry out of `a + b`, as `sltu` computes it from the sum and `b`. -/
theorem carry (a b : BitVec 64) :
    (a + b).toNat + 2 ^ 64 * (if a + b < b then (1 : BitVec 64) else 0).toNat =
      a.toNat + b.toNat := by
  have ha := a.isLt; have hb := b.isLt
  rw [BitVec.toNat_add]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat
  · have hlt : a + b < b := by
      rw [BitVec.lt_def, BitVec.toNat_add]; omega_using [ha, hb, h]
    simp only [hlt, ↓reduceIte]
    show _ + 2 ^ 64 * 1 = _
    omega_using [ha, hb, h]
  · have hlt : ¬ a + b < b := by
      rw [BitVec.lt_def, BitVec.toNat_add]; omega_using [ha, hb, h]
    simp only [hlt, ↓reduceIte]
    show _ + 2 ^ 64 * 0 = _
    omega_using [ha, hb, h]

theorem carry_le (c : Prop) [Decidable c] : (if c then (1 : BitVec 64) else 0).toNat ≤ 1 := by
  split <;> decide

/-- The words of a product. -/
theorem mul_words (a b : BitVec 64) :
    (a * b).toNat + 2 ^ 64 * (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat =
      a.toNat * b.toNat := by
  have hp : a.toNat * b.toNat < 2 ^ 128 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt) (by decide)
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
  generalize a.toNat * b.toNat = p at *
  omega_using [hp]

/-! ## The sequences -/

variable {s : State}

set_option linter.unusedSimpArgs false in
theorem mulWide_ok {lo hi a b : Reg} (hla : lo ≠ a := by decide) (hlb : lo ≠ b := by decide)
    (hlh : lo ≠ hi := by decide) :
    WP isa (.block (mulWide lo hi a b)) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat = (s.gpr a).toNat * (s.gpr b).toNat ∧
      Keeps [lo, hi] s s' := by
  apply WP.of_runBlock
  simp only [mulWide, runBlock_cons, runStep_some, runBlock_nil, exec_mul, exec_mulhu,
    RegUpd.gpr_write, Ne.symm hla, Ne.symm hlb, hlh, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨mul_words _ _, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

set_option linter.unusedSimpArgs false in
theorem add2_ok {lo hi x y : Reg} (hxl : x ≠ lo := by decide) (hhl : hi ≠ lo := by decide)
    (hhx : hi ≠ x := by decide) (hyl : y ≠ lo := by decide) (hyx : y ≠ x := by decide) :
    WP isa (.block (add2 lo hi x y)) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat =
        ((s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat +
          ((s.gpr x).toNat + 2 ^ 64 * (s.gpr y).toNat)) % 2 ^ 128 ∧
      Keeps [lo, hi, x] s s' := by
  apply WP.of_runBlock
  simp only [add2, runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu,
    RegUpd.gpr_write, hxl, hhl, hhx, hyl, hyx, Ne.symm hxl, Ne.symm hhl, Ne.symm hhx,
    ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have c := carry (s.gpr lo) (s.gpr x)
    have cl := carry_le (s.gpr lo + s.gpr x < s.gpr x)
    generalize (if s.gpr lo + s.gpr x < s.gpr x then (1 : BitVec 64) else 0) = k at *
    rw [BitVec.toNat_add (s.gpr hi + s.gpr y), BitVec.toNat_add (s.gpr hi)]
    have := (s.gpr hi).isLt; have := (s.gpr y).isLt
    have := (s.gpr lo + s.gpr x).isLt
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

theorem mulAdd_ok {lo hi t₁ t₂ a b : Reg} (h₁a : t₁ ≠ a := by decide) (h₁b : t₁ ≠ b := by decide)
    (h₁₂ : t₁ ≠ t₂ := by decide) (h₁l : t₁ ≠ lo := by decide) (h₁h : t₁ ≠ hi := by decide)
    (h₂l : t₂ ≠ lo := by decide) (h₂h : t₂ ≠ hi := by decide) (hhl : hi ≠ lo := by decide) :
    WP isa (.block (mulAdd lo hi t₁ t₂ a b)) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat =
        ((s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat + (s.gpr a).toNat * (s.gpr b).toNat) %
          2 ^ 128 ∧
      Keeps [lo, hi, t₁, t₂] s s' := by
  refine WP.block_append (WP.mono (mulWide_ok h₁a h₁b h₁₂) fun s₁ ⟨e₁, k₁⟩ => ?_)
  refine WP.mono (add2_ok h₁l hhl (Ne.symm h₁h) h₂l (Ne.symm h₁₂)) fun s₂ ⟨e₂, k₂⟩ => ?_
  refine ⟨?_, (k₁.trans k₂).mono fun r hr => ?_⟩
  · rw [e₂, e₁, k₁.1 lo (by simp [Ne.symm h₁l, Ne.symm h₂l]),
      k₁.1 hi (by simp [Ne.symm h₁h, Ne.symm h₂h])]
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (h | h) | (h | h | h) <;> simp only [h, true_or, or_true]

set_option linter.unusedSimpArgs false in
theorem mulAddSmall_ok {lo hi t a b : Reg} (htl : t ≠ lo := by decide) (hth : t ≠ hi := by decide)
    (hhl : hi ≠ lo := by decide) :
    WP isa (.block (mulAddSmall lo hi t a b)) s fun s' =>
      ((s.gpr a).toNat * (s.gpr b).toNat < 2 ^ 64 →
        (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat =
          ((s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat + (s.gpr a).toNat * (s.gpr b).toNat) %
            2 ^ 128) ∧
      Keeps [lo, hi, t] s s' := by
  apply WP.of_runBlock
  simp only [mulAddSmall, runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu, exec_mul,
    RegUpd.gpr_write, htl, hth, hhl, Ne.symm htl, Ne.symm hth, Ne.symm hhl,
    ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨fun hp => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have e : (s.gpr a * s.gpr b).toNat = (s.gpr a).toNat * (s.gpr b).toNat := by
      rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hp]
    have c := carry (s.gpr lo) (s.gpr a * s.gpr b)
    have cl := carry_le (s.gpr lo + s.gpr a * s.gpr b < s.gpr a * s.gpr b)
    generalize (if s.gpr lo + s.gpr a * s.gpr b < s.gpr a * s.gpr b then (1 : BitVec 64) else 0) = k at *
    rw [BitVec.toNat_add (s.gpr hi)]
    rw [e] at c
    have := (s.gpr hi).isLt
    have := (s.gpr lo + s.gpr a * s.gpr b).isLt
    generalize (s.gpr a).toNat * (s.gpr b).toNat = p at *
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- `w₀ + 2⁶⁴ w₁ + 2¹²⁸ w₂` in `s`. -/
abbrev val3 (s : State) (w₀ w₁ w₂ : Reg) : Nat :=
  (s.gpr w₀).toNat + 2 ^ 64 * (s.gpr w₁).toNat + 2 ^ 128 * (s.gpr w₂).toNat

set_option linter.unusedSimpArgs false in
theorem add3_ok {w₀ w₁ w₂ x₀ x₁ : Reg} (h₀₁ : w₀ ≠ w₁ := by decide) (h₀₂ : w₀ ≠ w₂ := by decide)
    (h₁₂ : w₁ ≠ w₂ := by decide) (hx : x₀ ≠ x₁ := by decide) (h₀x₀ : w₀ ≠ x₀ := by decide)
    (h₀x₁ : w₀ ≠ x₁ := by decide) (h₁x₀ : w₁ ≠ x₀ := by decide) (h₁x₁ : w₁ ≠ x₁ := by decide)
    (h₂x₀ : w₂ ≠ x₀ := by decide) (h₂x₁ : w₂ ≠ x₁ := by decide) :
    WP isa (.block (add3 w₀ w₁ w₂ x₀ x₁)) s fun s' =>
      val3 s' w₀ w₁ w₂ = (val3 s w₀ w₁ w₂ + ((s.gpr x₀).toNat + 2 ^ 64 * (s.gpr x₁).toNat)) % 2 ^ 192 ∧
      Keeps [w₀, w₁, w₂, x₀, x₁] s s' := by
  apply WP.of_runBlock
  simp only [add3, val3, runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu,
    RegUpd.gpr_write, h₀₁, h₀₂, h₁₂, hx, h₀x₀, h₀x₁, h₁x₀, h₁x₁, h₂x₀, h₂x₁, Ne.symm h₀₁,
    Ne.symm h₀₂, Ne.symm h₁₂, Ne.symm hx, Ne.symm h₀x₀, Ne.symm h₀x₁, Ne.symm h₁x₀, Ne.symm h₁x₁,
    Ne.symm h₂x₀, Ne.symm h₂x₁, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have c₀ := carry (s.gpr w₀) (s.gpr x₀)
    have l₀ := carry_le (s.gpr w₀ + s.gpr x₀ < s.gpr x₀)
    generalize (if s.gpr w₀ + s.gpr x₀ < s.gpr x₀ then (1 : BitVec 64) else 0) = k₀ at *
    have c₁ := carry (s.gpr w₁) (s.gpr x₁)
    have l₁ := carry_le (s.gpr w₁ + s.gpr x₁ < s.gpr x₁)
    generalize (if s.gpr w₁ + s.gpr x₁ < s.gpr x₁ then (1 : BitVec 64) else 0) = k₁ at *
    have c₂ := carry (s.gpr w₁ + s.gpr x₁) k₀
    have l₂ := carry_le (s.gpr w₁ + s.gpr x₁ + k₀ < k₀)
    generalize (if s.gpr w₁ + s.gpr x₁ + k₀ < k₀ then (1 : BitVec 64) else 0) = k₂ at *
    rw [BitVec.toNat_add (s.gpr w₂ + k₁), BitVec.toNat_add (s.gpr w₂)]
    have := (s.gpr w₂).isLt
    have := (s.gpr w₀ + s.gpr x₀).isLt
    have := (s.gpr w₁ + s.gpr x₁ + k₀).isLt
    have := (s.gpr w₁ + s.gpr x₁).isLt
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

set_option linter.unusedSimpArgs false in
theorem addW3_ok {d₀ d₁ d₂ a₀ a₁ a₂ t : Reg} (h₀₁ : d₀ ≠ d₁ := by decide)
    (h₀₂ : d₀ ≠ d₂ := by decide) (h₁₂ : d₁ ≠ d₂ := by decide) (h₀t : d₀ ≠ t := by decide)
    (h₁t : d₁ ≠ t := by decide) (h₂t : d₂ ≠ t := by decide) (h₀a₁ : d₀ ≠ a₁ := by decide)
    (h₀a₂ : d₀ ≠ a₂ := by decide) (h₁a₂ : d₁ ≠ a₂ := by decide) (hta₁ : t ≠ a₁ := by decide)
    (hta₂ : t ≠ a₂ := by decide) :
    WP isa (.block (addW3 d₀ d₁ d₂ a₀ a₁ a₂ t)) s fun s' =>
      val3 s' d₀ d₁ d₂ = (val3 s a₀ a₁ a₂ + (s.gpr t).toNat) % 2 ^ 192 ∧
      Keeps [d₀, d₁, d₂, t] s s' := by
  apply WP.of_runBlock
  simp only [addW3, val3, runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu,
    RegUpd.gpr_write, h₀₁, h₀₂, h₁₂, h₀t, h₁t, h₂t, h₀a₁, h₀a₂, h₁a₂, hta₁, hta₂, Ne.symm h₀₁,
    Ne.symm h₀₂, Ne.symm h₁₂, Ne.symm h₀t, Ne.symm h₁t, Ne.symm h₂t, Ne.symm h₀a₁, Ne.symm h₀a₂,
    Ne.symm h₁a₂, Ne.symm hta₁, Ne.symm hta₂, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have c₀ := carry (s.gpr a₀) (s.gpr t)
    have l₀ := carry_le (s.gpr a₀ + s.gpr t < s.gpr t)
    generalize (if s.gpr a₀ + s.gpr t < s.gpr t then (1 : BitVec 64) else 0) = k₀ at *
    have c₁ := carry (s.gpr a₁) k₀
    have l₁ := carry_le (s.gpr a₁ + k₀ < k₀)
    generalize (if s.gpr a₁ + k₀ < k₀ then (1 : BitVec 64) else 0) = k₁ at *
    rw [BitVec.toNat_add (s.gpr a₂)]
    have := (s.gpr a₂).isLt
    have := (s.gpr a₀ + s.gpr t).isLt
    have := (s.gpr a₁ + k₀).isLt
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

end VG.RISCV64.Wide
