module

import VerifiedGarbage.Proof.Mont.AArch64.Csub
public import VerifiedGarbage.Proof.Framework.PowLit
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# P-384's Montgomery product on AArch64: one short reduction

`montreds d₀ … d₅` (`Impl/Mont/AArch64/P384Mul.lean`) takes `[d₅ … d₀]` to
`([d₅ … d₀] + w p) / 2^64` with `w = d₀ (2^32 + 1) mod 2^64` (`montreds_ok`):
`w` into `d₀`'s register (`wStep_ok`), the three words of
`(2^384 - p) w / 2^64` into `x1`–`x3` (`xStep_ok`), and their difference
with `[w d₅ … d₁]` (`sStep_ok`), which cannot borrow (`montreds_arith`).
-/

@[expose] public section

-- Powers of two up to `2^448` (the product's rows) are evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.Mont.AArch64.P384Mul

open VG VG.AArch64 VG.Impl.Mont.AArch64.P384Mul VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut Word64.addCarry_value)

/-- P-384's prime. -/
abbrev p : Nat := 2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1

/-- The low word of `2^384 - p`, in `x16`. -/
abbrev c0 : BitVec 64 := 0xffffffff00000001

/-- The next word of `2^384 - p`, in `x17` (the word above it is `1`). -/
abbrev c1 : BitVec 64 := 0x00000000ffffffff

/-- `w = d₀ (2^32 + 1)`, into `d₀`'s register. -/
theorem wStep_ok (s : State) {d₀ : Reg} (h : d₀ ≠ .x1) :
    WP isa (.block [.lsl .x .x1 d₀ 32, .add .x d₀ .x1 d₀]) s fun t =>
      t.gpr d₀ = (s.gpr d₀ <<< 32) + s.gpr d₀ ∧ t.c = s.c ∧ Keeps [.x1, d₀] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show 32 < Size.x.bits by decide,
    ite_true, RegUpd.gpr_write, RegUpd.c_write, BitVec.setWidth_eq, h, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- `[x3 x2 x1] = ⌊c0 w / 2^64⌋ + c1 w + 2^64 w`: the words of `(2^384 - p) w`
but the lowest. -/
theorem xStep_ok (s : State) {d₀ : Reg} (h1 : d₀ ≠ .x1) (h2 : d₀ ≠ .x2) (h3 : d₀ ≠ .x3)
    (hz : s.gpr .x7 = 0) :
    WP isa (.block [.umulh .x1 .x16 d₀, .mul .x .x3 .x17 d₀, .umulh .x2 .x17 d₀,
        .adds .x .x1 .x1 .x3, .adcs .x .x2 .x2 d₀, .adc .x .x3 .x7 .x7]) s fun t =>
      (t.gpr .x1).toNat + 2 ^ 64 * (t.gpr .x2).toNat + 2 ^ 128 * (t.gpr .x3).toNat =
        (s.gpr .x16).toNat * (s.gpr d₀).toNat / 2 ^ 64 + (s.gpr .x17).toNat * (s.gpr d₀).toNat +
          2 ^ 64 * (s.gpr d₀).toNat ∧
      Keeps [.x1, .x2, .x3] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, h1, h2, h3, ite_false, ite_true, reduceCtorEq, hz,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have e1 := Word64.addCarry_value (BitVec.ofNat 64 ((s.gpr .x16).toNat * (s.gpr d₀).toNat / 2 ^ 64))
      (s.gpr .x17 * s.gpr d₀) false
    have e2 := Word64.addCarry_value (BitVec.ofNat 64 ((s.gpr .x17).toNat * (s.gpr d₀).toNat / 2 ^ 64))
      (s.gpr d₀) (Word64.carryOut (BitVec.ofNat 64 ((s.gpr .x16).toNat * (s.gpr d₀).toNat / 2 ^ 64))
        (s.gpr .x17 * s.gpr d₀) false)
    have m1 := VG.Proof.Ed25519.AArch64.mul_lo_hi (s.gpr .x16) (s.gpr d₀)
    have m2 := VG.Proof.Ed25519.AArch64.mul_lo_hi (s.gpr .x17) (s.gpr d₀)
    simp only [VG.Proof.Ed25519.AArch64.mulHi] at m1 m2
    simp only [Word64.addCarry, Word64.carryOut] at e1 e2
    have hc : ∀ c : Bool, ((0 : BitVec 64) + 0 + BitVec.ofNat 64 c.toNat).toNat = c.toNat := by
      intro c; cases c <;> rfl
    dsimp only [Size.bits] at hc ⊢
    rw [hc]
    have := (s.gpr .x16).isLt
    have := (s.gpr d₀).isLt
    simp only [BitVec.toNat_ofNat, Bool.toNat_false] at e1 e2 m1 m2 ⊢
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr, ite_false]

/-- `d = d + ~0 + c` (`sbc` of `x7 = 0`): `d` less the borrow `!c`, modulo `2^64`. -/
theorem sbc0_ok (s : State) (d : Reg) (hz : s.gpr .x7 = 0) :
    WP isa (.block [.sbc .x d d .x7]) s fun t =>
      (∃ j, (t.gpr d).toNat + (!s.c).toNat = (s.gpr d).toNat + 2 ^ 64 * j) ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, ite_true, hz, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have e := Word64.addCarry_value (s.gpr d) (~~~0) s.c
    refine ⟨1 - (Word64.carryOut (s.gpr d) (~~~0) s.c).toNat, ?_⟩
    change (Word64.addCarry (s.gpr d) (~~~0) s.c).toNat + _ = _
    have hn : (~~~(0 : BitVec 64)).toNat = 2 ^ 64 - 1 := rfl
    rw [hn] at e
    have hb : ∀ c, (Word64.carryOut (s.gpr d) (~~~0) c).toNat ≤ 1 := fun c => Bool.toNat_le _
    revert e
    cases s.c <;> intro e <;> have := hb false <;> have := hb true <;>
      simp only [Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false] at e ⊢ <;> omega_arith
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

/-- `[d₀ d₅ d₄ d₃ d₂ d₁] -= [x3 x2 x1]`, modulo `2^384`. -/
theorem sStep_ok (s : State) {d₀ d₁ d₂ d₃ d₄ d₅ : Reg}
    (hf : [d₀, d₁, d₂, d₃, d₄, d₅, .x1, .x2, .x3, .x7].Nodup) (hz : s.gpr .x7 = 0) :
    WP isa (.block [.subs .x d₁ d₁ .x1, .sbcs .x d₂ d₂ .x2, .sbcs .x d₃ d₃ .x3, .sbcs .x d₄ d₄ .x7,
        .sbcs .x d₅ d₅ .x7, .sbc .x d₀ d₀ .x7]) s fun t =>
      (∃ j, regsVal t [d₁, d₂, d₃, d₄, d₅, d₀] + regsVal s [.x1, .x2, .x3] =
        regsVal s [d₁, d₂, d₃, d₄, d₅, d₀] + 2 ^ 384 * j) ∧ Keeps [d₁, d₂, d₃, d₄, d₅, d₀] s t := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hf
  obtain ⟨⟨h01, h02, h03, h04, h05, h0x1, h0x2, h0x3, h0x7⟩, ⟨h12, h13, h14, h15, h1x1, h1x2, h1x3, h1x7⟩,
    ⟨h23, h24, h25, h2x1, h2x2, h2x3, h2x7⟩, ⟨h34, h35, h3x1, h3x2, h3x3, h3x7⟩,
    ⟨h45, h4x1, h4x2, h4x3, h4x7⟩, ⟨h5x1, h5x2, h5x3, h5x7⟩, -⟩ := hf
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (subc_ok s d₁ d₁ .x1 true rfl) fun s₁ ⟨v₁, c₁, k₁⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (subc_ok s₁ d₂ d₂ .x2 false rfl) fun s₂ ⟨v₂, c₂, k₂⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (subc_ok s₂ d₃ d₃ .x3 false rfl) fun s₃ ⟨v₃, c₃, k₃⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (subc_ok s₃ d₄ d₄ .x7 false rfl) fun s₄ ⟨v₄, c₄, k₄⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (subc_ok s₄ d₅ d₅ .x7 false rfl) fun s₅ ⟨v₅, c₅, k₅⟩ => ?_
  have z₅ : s₅.gpr .x7 = 0 := by
    rw [k₅.gpr _ (by simpa using Ne.symm h5x7), k₄.gpr _ (by simpa using Ne.symm h4x7),
      k₃.gpr _ (by simpa using Ne.symm h3x7), k₂.gpr _ (by simpa using Ne.symm h2x7),
      k₁.gpr _ (by simpa using Ne.symm h1x7), hz]
  refine WP.mono (sbc0_ok s₅ d₀ z₅) fun t ⟨⟨j, v₆⟩, k₆⟩ => ?_
  refine ⟨?_, (k₁.mono (by sub_regs)).trans ((k₂.mono (by sub_regs)).trans ((k₃.mono (by sub_regs)).trans
    ((k₄.mono (by sub_regs)).trans ((k₅.mono (by sub_regs)).trans (k₆.mono (by sub_regs))))))⟩
  -- Each word's value, read through the later writes.
  have g₁ : t.gpr d₁ = s₁.gpr d₁ := by
    rw [k₆.gpr _ (by simpa using Ne.symm h01), k₅.gpr _ (by simpa using h15),
      k₄.gpr _ (by simpa using h14), k₃.gpr _ (by simpa using h13), k₂.gpr _ (by simpa using h12)]
  have g₂ : t.gpr d₂ = s₂.gpr d₂ := by
    rw [k₆.gpr _ (by simpa using Ne.symm h02), k₅.gpr _ (by simpa using h25),
      k₄.gpr _ (by simpa using h24), k₃.gpr _ (by simpa using h23)]
  have g₃ : t.gpr d₃ = s₃.gpr d₃ := by
    rw [k₆.gpr _ (by simpa using Ne.symm h03), k₅.gpr _ (by simpa using h35), k₄.gpr _ (by simpa using h34)]
  have g₄ : t.gpr d₄ = s₄.gpr d₄ := by
    rw [k₆.gpr _ (by simpa using Ne.symm h04), k₅.gpr _ (by simpa using h45)]
  have g₅ : t.gpr d₅ = s₅.gpr d₅ := by rw [k₆.gpr _ (by simpa using Ne.symm h05)]
  -- The inputs, read through the earlier writes.
  have i₂ : s₁.gpr d₂ = s.gpr d₂ := k₁.gpr _ (by simpa using Ne.symm h12)
  have i₃ : s₂.gpr d₃ = s.gpr d₃ := by
    rw [k₂.gpr _ (by simpa using Ne.symm h23), k₁.gpr _ (by simpa using Ne.symm h13)]
  have i₄ : s₃.gpr d₄ = s.gpr d₄ := by
    rw [k₃.gpr _ (by simpa using Ne.symm h34), k₂.gpr _ (by simpa using Ne.symm h24),
      k₁.gpr _ (by simpa using Ne.symm h14)]
  have i₅ : s₄.gpr d₅ = s.gpr d₅ := by
    rw [k₄.gpr _ (by simpa using Ne.symm h45), k₃.gpr _ (by simpa using Ne.symm h35),
      k₂.gpr _ (by simpa using Ne.symm h25), k₁.gpr _ (by simpa using Ne.symm h15)]
  have i₀ : s₅.gpr d₀ = s.gpr d₀ := by
    rw [k₅.gpr _ (by simpa using h05), k₄.gpr _ (by simpa using h04),
      k₃.gpr _ (by simpa using h03), k₂.gpr _ (by simpa using h02), k₁.gpr _ (by simpa using h01)]
  have x₂ : s₁.gpr .x2 = s.gpr .x2 := k₁.gpr _ (by simpa using Ne.symm h1x2)
  have x₃ : s₂.gpr .x3 = s.gpr .x3 := by
    rw [k₂.gpr _ (by simpa using Ne.symm h2x3), k₁.gpr _ (by simpa using Ne.symm h1x3)]
  have x₇₃ : s₃.gpr .x7 = 0 := by
    rw [k₃.gpr _ (by simpa using Ne.symm h3x7), k₂.gpr _ (by simpa using Ne.symm h2x7),
      k₁.gpr _ (by simpa using Ne.symm h1x7), hz]
  have x₇₄ : s₄.gpr .x7 = 0 := by rw [k₄.gpr _ (by simpa using Ne.symm h4x7), x₇₃]
  have e₁ := sub_borrow (s.gpr d₁) (s.gpr .x1) true
  have e₂ := sub_borrow (s₁.gpr d₂) (s₁.gpr .x2) s₁.c
  have e₃ := sub_borrow (s₂.gpr d₃) (s₂.gpr .x3) s₂.c
  have e₄ := sub_borrow (s₃.gpr d₄) (s₃.gpr .x7) s₃.c
  have e₅ := sub_borrow (s₄.gpr d₅) (s₄.gpr .x7) s₄.c
  simp only [ite_true, ite_false, Bool.false_eq_true] at v₁ c₁ v₂ c₂ v₃ c₃ v₄ c₄ v₅ c₅
  rw [← v₁, ← c₁] at e₁
  rw [← v₂, ← c₂] at e₂
  rw [← v₃, ← c₃] at e₃
  rw [← v₄, ← c₄] at e₄
  rw [← v₅, ← c₅] at e₅
  rw [i₂, x₂] at e₂
  rw [i₃, x₃] at e₃
  rw [i₄, x₇₃] at e₄
  rw [i₅, x₇₄] at e₅
  rw [i₀] at v₆
  refine ⟨j, ?_⟩
  simp only [regsVal, g₁, g₂, g₃, g₄, g₅]
  simp only [Bool.not_true, Bool.toNat_false, show (0 : BitVec 64).toNat = 0 from rfl] at e₁ e₄ e₅
  have := Bool.toNat_le (!s₁.c); have := Bool.toNat_le (!s₂.c); have := Bool.toNat_le (!s₃.c)
  have := Bool.toNat_le (!s₄.c); have := Bool.toNat_le (!s₅.c)
  omega_arith

/-- `w p` cancels `d₀`, the low word of `[d₅ … d₀]`: `c0 w ≡ d₀`. -/
theorem low_cancel {a W : Nat} (hW : W = (a * 2 ^ 32 % 2 ^ 64 + a) % 2 ^ 64) (ha : a < 2 ^ 64) :
    0xffffffff00000001 * W % 2 ^ 64 = a := by
  subst hW
  omega_arith

/-- The reduction's arithmetic: `[x3 x2 x1] = X` subtracted from `[w d₅ … d₁]`
does not borrow, and leaves `([d₅ … d₀] + w p) / 2^64`. -/
theorem montreds_arith {a W X T L j : Nat} (ha : a < 2 ^ 64)
    (hW : W = (a * 2 ^ 32 % 2 ^ 64 + a) % 2 ^ 64)
    (hX : X = 0xffffffff00000001 * W / 2 ^ 64 + 0xffffffff * W + 2 ^ 64 * W)
    (hS : T + X = L + 2 ^ 320 * W + 2 ^ 384 * j) (hT : T < 2 ^ 384) (hL : L < 2 ^ 320) :
    2 ^ 64 * T = a + 2 ^ 64 * L + W * p := by
  have hc := low_cancel hW ha
  have hW64 : W < 2 ^ 64 := by omega_arith
  have hdiv := Nat.div_add_mod (0xffffffff00000001 * W) (2 ^ 64)
  rw [hc] at hdiv
  rw [show W * p = W * 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319
    from rfl]
  omega_arith

/-- One short reduction: `[d₀ d₅ … d₁] = ([d₅ … d₀] + w p) / 2^64` for some
word `w`. -/
theorem montreds_ok (s : State) {d₀ d₁ d₂ d₃ d₄ d₅ : Reg}
    (hf : [d₀, d₁, d₂, d₃, d₄, d₅, .x1, .x2, .x3, .x7, .x16, .x17].Nodup) (hz : s.gpr .x7 = 0)
    (h16 : s.gpr .x16 = c0) (h17 : s.gpr .x17 = c1) :
    WP isa (.block (montreds d₀ d₁ d₂ d₃ d₄ d₅)) s fun t =>
      (∃ w < 2 ^ 64, 2 ^ 64 * regsVal t [d₁, d₂, d₃, d₄, d₅, d₀] =
        regsVal s [d₀, d₁, d₂, d₃, d₄, d₅] + w * p) ∧
      Keeps [.x1, .x2, .x3, d₀, d₁, d₂, d₃, d₄, d₅] s t := by
  have hf' : [d₀, d₁, d₂, d₃, d₄, d₅, .x1, .x2, .x3, .x7].Nodup :=
    (List.Sublist.nodup (by simp) hf)
  have hn := hf
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨⟨h01, h02, h03, h04, h05, h0x1, h0x2, h0x3, h0x7, h0x16, h0x17⟩,
    ⟨h12, h13, h14, h15, h1x1, h1x2, h1x3, -, -, -⟩, ⟨h23, h24, h25, h2x1, h2x2, h2x3, -, -, -⟩,
    ⟨h34, h35, h3x1, h3x2, h3x3, -, -, -⟩, ⟨h45, h4x1, h4x2, h4x3, -, -, -⟩,
    ⟨h5x1, h5x2, h5x3, -, -, -⟩, -⟩ := hn
  have split : ∀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ i₉ i₁₀ i₁₁ i₁₂ i₁₃ i₁₄ : Instr,
      [i₁, i₂, i₃, i₄, i₅, i₆, i₇, i₈, i₉, i₁₀, i₁₁, i₁₂, i₁₃, i₁₄] =
        [i₁, i₂] ++ ([i₃, i₄, i₅, i₆, i₇, i₈] ++ [i₉, i₁₀, i₁₁, i₁₂, i₁₃, i₁₄]) :=
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  rw [montreds, split, WP.block_append_iff]
  refine WP.mono (wStep_ok s h0x1) fun s₁ ⟨w₁, _, k₁⟩ => ?_
  have z₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (by simpa using Ne.symm h0x7), hz]
  rw [WP.block_append_iff]
  refine WP.mono (xStep_ok s₁ h0x1 h0x2 h0x3 z₁) fun s₂ ⟨x₂, k₂⟩ => ?_
  have z₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by decide), z₁]
  refine WP.mono (sStep_ok s₂ hf' z₂) fun t ⟨⟨j, hS⟩, k₃⟩ => ?_
  refine ⟨?_, (k₁.mono (by sub_regs)).trans ((k₂.mono (by sub_regs)).trans (k₃.mono (by sub_regs)))⟩
  have g16 : s₁.gpr .x16 = c0 := by rw [k₁.gpr _ (by simpa using Ne.symm h0x16), h16]
  have g17 : s₁.gpr .x17 = c1 := by rw [k₁.gpr _ (by simpa using Ne.symm h0x17), h17]
  rw [g16, g17] at x₂
  have gd : ∀ r, r ≠ d₀ → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → s₂.gpr r = s.gpr r := fun r a b c d => by
    rw [k₂.gpr _ (by simp [b, c, d]), k₁.gpr _ (by simp [a, b])]
  have w₂ : s₂.gpr d₀ = s.gpr d₀ <<< 32 + s.gpr d₀ := by
    rw [k₂.gpr _ (by simp [h0x1, h0x2, h0x3]), w₁]
  have hW : (s.gpr d₀ <<< 32 + s.gpr d₀).toNat =
      ((s.gpr d₀).toNat * 2 ^ 32 % 2 ^ 64 + (s.gpr d₀).toNat) % 2 ^ 64 := by
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  refine ⟨(s.gpr d₀ <<< 32 + s.gpr d₀).toNat, BitVec.isLt _, ?_⟩
  have hX : regsVal s₂ [.x1, .x2, .x3] =
      0xffffffff00000001 * (s.gpr d₀ <<< 32 + s.gpr d₀).toNat / 2 ^ 64 +
        0xffffffff * (s.gpr d₀ <<< 32 + s.gpr d₀).toNat + 2 ^ 64 * (s.gpr d₀ <<< 32 + s.gpr d₀).toNat := by
    rw [w₁] at x₂
    simp only [regsVal]
    rw [show c0.toNat = 0xffffffff00000001 from rfl, show c1.toNat = 0xffffffff from rfl] at x₂
    omega_arith
  have hD : regsVal s₂ [d₁, d₂, d₃, d₄, d₅, d₀] =
      regsVal s [d₁, d₂, d₃, d₄, d₅] + 2 ^ 320 * (s.gpr d₀ <<< 32 + s.gpr d₀).toNat := by
    simp only [regsVal, gd d₁ (Ne.symm h01) h1x1 h1x2 h1x3, gd d₂ (Ne.symm h02) h2x1 h2x2 h2x3,
      gd d₃ (Ne.symm h03) h3x1 h3x2 h3x3, gd d₄ (Ne.symm h04) h4x1 h4x2 h4x3,
      gd d₅ (Ne.symm h05) h5x1 h5x2 h5x3, w₂]
    omega_arith
  rw [hX, hD] at hS
  have hT := regsVal_lt t [d₁, d₂, d₃, d₄, d₅, d₀]
  have hL := regsVal_lt s [d₁, d₂, d₃, d₄, d₅]
  simp only [List.length_cons, List.length_nil] at hT hL
  rw [regsVal]
  exact montreds_arith (s.gpr d₀).isLt hW rfl hS hT hL

/-- `x16 = c0` and `x17 = c1`, `x7` being zero. -/
theorem redConsts_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block redConsts) s fun t => t.gpr .x16 = c0 ∧ t.gpr .x17 = c1 ∧ Keeps [.x16, .x17] s t := by
  apply WP.of_runBlock
  simp only [redConsts, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    show (1 : Nat) < 4096 from by decide, show 32 < Size.x.bits from by decide, ite_true,
    RegUpd.gpr_write, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left', hz, reduceCtorEq, ite_false]
  refine ⟨by decide, by decide, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- The low half's registers after `k` reductions, word `0` first. -/
def rot (k : Nat) : List Reg := (List.range 6).map (lowAt k)

theorem rot_zero : rot 0 = lowRegs := by decide

theorem rot_six : rot 6 = lowRegs := by decide

/-- Reduction `k` reads the registers `rot k` and leaves them as `rot (k + 1)`. -/
theorem rot_facts : ∀ k < 6,
    [lowAt k 0, lowAt k 1, lowAt k 2, lowAt k 3, lowAt k 4, lowAt k 5] = rot k ∧
    [lowAt k 1, lowAt k 2, lowAt k 3, lowAt k 4, lowAt k 5, lowAt k 0] = rot (k + 1) ∧
    [lowAt k 0, lowAt k 1, lowAt k 2, lowAt k 3, lowAt k 4, lowAt k 5,
      .x1, .x2, .x3, .x7, .x16, .x17].Nodup ∧
    ∀ r ∈ [Reg.x1, .x2, .x3, lowAt k 0, lowAt k 1, lowAt k 2, lowAt k 3, lowAt k 4, lowAt k 5],
      r ∈ [Reg.x1, .x2, .x3] ++ lowRegs := by
  decide

/-- The first `n` reductions: `[rot n] = ([low] + W p) / 2^(64 n)`. -/
theorem redsN_ok : ∀ n ≤ 6, ∀ (s : State), s.gpr .x7 = 0 → s.gpr .x16 = c0 → s.gpr .x17 = c1 →
    WP isa (.block ((List.range n).flatMap red)) s fun t =>
      (∃ W < 2 ^ (64 * n), 2 ^ (64 * n) * regsVal t (rot n) = regsVal s lowRegs + W * p) ∧
      Keeps (([.x1, .x2, .x3] : List Reg) ++ lowRegs) s t
  | 0, _, s, _, _, _ => WP.block_nil ⟨⟨0, by decide, by rw [rot_zero]; simp⟩, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, hn, s, hz, h16, h17 => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (redsN_ok n (by omega_arith) s hz h16 h17) fun s₁ ⟨⟨W, hW, e₁⟩, k₁⟩ => ?_
    obtain ⟨r0, r1, hnd, hsub⟩ := rot_facts n (by omega_arith)
    have kx : ∀ r, r ∉ [Reg.x1, .x2, .x3] ++ lowRegs → s₁.gpr r = s.gpr r := k₁.gpr
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (montreds_ok s₁ hnd (by rw [kx _ (by decide), hz]) (by rw [kx _ (by decide), h16])
      (by rw [kx _ (by decide), h17])) fun t ⟨⟨w, hw, e₂⟩, k₂⟩ => ?_
    refine ⟨?_, k₁.trans (k₂.mono hsub)⟩
    rw [r0] at e₂
    rw [r1] at e₂
    refine ⟨W + 2 ^ (64 * n) * w, ?_, ?_⟩
    · have : 2 ^ (64 * n) * w ≤ 2 ^ (64 * n) * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega_arith)
      rw [show 64 * (n + 1) = 64 * n + 64 by omega_arith, Nat.pow_add]
      omega_arith
    · rw [show 64 * (n + 1) = 64 * n + 64 by omega_arith, Nat.pow_add, Nat.mul_assoc, e₂, Nat.mul_add, e₁,
        Nat.add_mul, Nat.add_assoc, Nat.mul_assoc]

/-- `x16` and `x17` set, then the six reductions: `2^384 [low'] = [low] + W p`. -/
theorem reds_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block reds) s fun t =>
      (∃ W < 2 ^ 384, 2 ^ 384 * regsVal t lowRegs = regsVal s lowRegs + W * p) ∧
      Keeps (([.x16, .x17] : List Reg) ++ (([.x1, .x2, .x3] : List Reg) ++ lowRegs)) s t := by
  rw [reds, WP.block_append_iff]
  refine WP.mono (redConsts_ok s hz) fun s₁ ⟨h16, h17, k₁⟩ => ?_
  have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (by decide), hz]
  have hl : regsVal s₁ lowRegs = regsVal s lowRegs :=
    regsVal_congr fun r hr => k₁.gpr r (by revert r; decide)
  refine WP.mono (redsN_ok 6 (by decide) s₁ hz₁ h16 h17) fun t ⟨⟨W, hW, e⟩, k₂⟩ => ?_
  rw [rot_six, hl] at e
  exact ⟨⟨W, hW, e⟩, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩

end VG.Proof.Mont.AArch64.P384Mul
