module

import VerifiedGarbage.Proof.Framework.OmegaNear
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalStep
public import VerifiedGarbage.Impl.Bignum.X86_64.BaseSquare
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd

/-!
# The baseline square's diagonal step (x86-64)

`core`: two words of the cross products doubled, the square of
`rdx` and the carry word `r15` added, by `mul`, `add` and `adc`
(`core_coreOk`, `AdxSquare.CoreOk`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.BaseSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.BaseSquare VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem add_toNat64 (x y : BitVec 64) :
    (x + y).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ x.toNat + y.toNat)).toNat = x.toNat + y.toNat := by
  have := x.isLt; have := y.isLt
  rw [BitVec.toNat_add]
  by_cases h : 2 ^ 64 ≤ x.toNat + y.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega_near

/-- `add`, `adc`, `adc 0`: `x0 + 2⁶⁴ x1 + 2¹²⁸ x2` plus `y0 + 2⁶⁴ y1`, if it fits. -/
theorem chain3 (x0 x1 x2 y0 y1 : BitVec 64)
    (h : x0.toNat + y0.toNat + 2 ^ 64 * (x1.toNat + y1.toNat) + 2 ^ 128 * x2.toNat < 2 ^ 192) :
    (x0 + y0).toNat + 2 ^ 64 * (x1 + y1 + (BitVec.ofBool (decide (2 ^ 64 ≤ x0.toNat + y0.toNat))).setWidth 64).toNat +
      2 ^ 128 * (x2 + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ x1.toNat + y1.toNat +
        (decide (2 ^ 64 ≤ x0.toNat + y0.toNat)).toNat))).setWidth 64).toNat =
      x0.toNat + y0.toNat + 2 ^ 64 * (x1.toNat + y1.toNat) + 2 ^ 128 * x2.toNat := by
  have e0 := add_toNat64 x0 y0
  have e1 := adc_toNat x1 y1 (decide (2 ^ 64 ≤ x0.toNat + y0.toNat))
  have e2 := adc_toNat x2 0 (decide (2 ^ 64 ≤ x1.toNat + y1.toNat + (decide (2 ^ 64 ≤ x0.toNat + y0.toNat)).toNat))
  have z : (0 : BitVec 64).toNat = 0 := rfl
  rw [z] at e2
  have : decide (2 ^ 64 ≤ x2.toNat + 0 + (decide (2 ^ 64 ≤ x1.toNat + y1.toNat +
      (decide (2 ^ 64 ≤ x0.toNat + y0.toNat)).toNat)).toNat) = false := by
    simp only [decide_eq_false_iff_not, Nat.not_le]
    have := (x0 + y0).isLt
    have := (x1 + y1 + (BitVec.ofBool (decide (2 ^ 64 ≤ x0.toNat + y0.toNat))).setWidth 64).isLt
    omega_near
  rw [this, Bool.toNat_false] at e2
  omega_near

theorem core0_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .rdx), .mov .rsi (.reg .rdx), .mul .rsi, .mov32 .rbx (.imm 0)]) s fun t =>
      (t.gpr .rax).toNat + 2 ^ 64 * (t.gpr .rdx).toNat = (s.gpr .rdx).toNat * (s.gpr .rdx).toNat ∧
      t.gpr .rsi = s.gpr .rdx ∧ t.gpr .rbx = 0 ∧ t.mem = s.mem ∧ Keep [.rax, .rsi, .rdx, .rbx] s t := by
  refine WP.mono (WP.keep [.rax, .rsi, .rdx, .rbx] (Q := fun t =>
    (t.gpr .rax).toNat + 2 ^ 64 * (t.gpr .rdx).toNat = (s.gpr .rdx).toNat * (s.gpr .rdx).toNat ∧
      t.gpr .rsi = s.gpr .rdx ∧ t.gpr .rbx = 0 ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  xrun
  exact mul_toNat _ _

theorem core1_ok (s : State)
    (h : 2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) + 2 ^ 128 * (s.gpr .rbx).toNat < 2 ^ 192) :
    WP isa (.block [.alu .add .r11 (.reg .r11), .alu .adc .r12 (.reg .r12), .alu .adc .rbx (.imm 0)]) s fun t =>
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .rbx).toNat =
        2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) + 2 ^ 128 * (s.gpr .rbx).toNat ∧
      t.mem = s.mem ∧ Keep [.r11, .r12, .rbx] s t := by
  refine WP.mono (WP.keep [.r11, .r12, .rbx] (Q := fun t =>
    (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .rbx).toNat =
        2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) + 2 ^ 128 * (s.gpr .rbx).toNat ∧
      t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  xrun [sx0]
  rw [chain3 _ _ _ _ _ (by omega_near)]
  omega_near

theorem core2_ok (s : State)
    (h : (s.gpr .r11).toNat + (s.gpr .rax).toNat + 2 ^ 64 * ((s.gpr .r12).toNat + (s.gpr .rdx).toNat) +
      2 ^ 128 * (s.gpr .rbx).toNat < 2 ^ 192) :
    WP isa (.block [.alu .add .r11 (.reg .rax), .alu .adc .r12 (.reg .rdx), .alu .adc .rbx (.imm 0)]) s fun t =>
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .rbx).toNat =
        (s.gpr .r11).toNat + (s.gpr .rax).toNat + 2 ^ 64 * ((s.gpr .r12).toNat + (s.gpr .rdx).toNat) +
          2 ^ 128 * (s.gpr .rbx).toNat ∧
      t.mem = s.mem ∧ Keep [.r11, .r12, .rbx] s t := by
  refine WP.mono (WP.keep [.r11, .r12, .rbx] (Q := fun t =>
    (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .rbx).toNat =
        (s.gpr .r11).toNat + (s.gpr .rax).toNat + 2 ^ 64 * ((s.gpr .r12).toNat + (s.gpr .rdx).toNat) +
          2 ^ 128 * (s.gpr .rbx).toNat ∧
      t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  xrun [sx0]
  exact chain3 _ _ _ _ _ h

theorem core3_ok (s : State)
    (h : (s.gpr .r11).toNat + (s.gpr .r15).toNat + 2 ^ 64 * (s.gpr .r12).toNat +
      2 ^ 128 * (s.gpr .rbx).toNat < 2 ^ 192) :
    WP isa (.block [.alu .add .r11 (.reg .r15), .alu .adc .r12 (.imm 0), .alu .adc .rbx (.imm 0)]) s fun t =>
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .rbx).toNat =
        (s.gpr .r11).toNat + (s.gpr .r15).toNat + 2 ^ 64 * (s.gpr .r12).toNat + 2 ^ 128 * (s.gpr .rbx).toNat ∧
      t.mem = s.mem ∧ Keep [.r11, .r12, .rbx] s t := by
  refine WP.mono (WP.keep [.r11, .r12, .rbx] (Q := fun t =>
    (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .rbx).toNat =
        (s.gpr .r11).toNat + (s.gpr .r15).toNat + 2 ^ 64 * (s.gpr .r12).toNat + 2 ^ 128 * (s.gpr .rbx).toNat ∧
      t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  xrun [sx0]
  have := chain3 (s.gpr .r11) (s.gpr .r12) (s.gpr .rbx) (s.gpr .r15) 0 (by
    rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega_near)
  simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at this ⊢
  exact this

/-- `core`'s result, as `AdxSquare.diagonalCore`'s. -/
theorem core_ok (s : State) :
    WP isa (.block core) s fun t =>
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .rbx).toNat =
        2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) +
          (s.gpr .rdx).toNat * (s.gpr .rdx).toNat + (s.gpr .r15).toNat ∧
      Keeps [.rsi, .rbx, .rax, .rcx, .r11, .r12] s t := by
  rw [show core =
    ([.mov .rax (.reg .rdx), .mov .rsi (.reg .rdx), .mul .rsi, .mov32 .rbx (.imm 0)] : List Instr) ++
    (([.alu .add .r11 (.reg .r11), .alu .adc .r12 (.reg .r12), .alu .adc .rbx (.imm 0)] : List Instr) ++
    (([.alu .add .r11 (.reg .rax), .alu .adc .r12 (.reg .rdx), .alu .adc .rbx (.imm 0)] : List Instr) ++
    (([.alu .add .r11 (.reg .r15), .alu .adc .r12 (.imm 0), .alu .adc .rbx (.imm 0)] : List Instr) ++
    ([.mov .rdx (.reg .rsi)] : List Instr)))) from rfl]
  have hx0 := (s.gpr .r11).isLt
  have hx1 := (s.gpr .r12).isLt
  have hc := (s.gpr .r15).isLt
  have hsq := mul_le (s.gpr .rdx) (s.gpr .rdx)
  rw [WP.block_append_iff]
  refine WP.mono (core0_ok s) fun s₁ ⟨hp, hsi, hbx, hm₁, k₁⟩ => ?_
  have e11 : s₁.gpr .r11 = s.gpr .r11 := k₁.gpr (by decide)
  have e12 : s₁.gpr .r12 = s.gpr .r12 := k₁.gpr (by decide)
  have e15 : s₁.gpr .r15 = s.gpr .r15 := k₁.gpr (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (core1_ok s₁ (by rw [e11, e12, hbx, show (0 : BitVec 64).toNat = 0 from rfl]; omega_near))
    fun s₂ ⟨hv₂, hm₂, k₂⟩ => ?_
  rw [e11, e12, hbx, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero] at hv₂
  have r2ax : s₂.gpr .rax = s₁.gpr .rax := k₂.gpr (by decide)
  have r2dx : s₂.gpr .rdx = s₁.gpr .rdx := k₂.gpr (by decide)
  have hb₂ := (s₂.gpr .r11).isLt
  rw [WP.block_append_iff]
  refine WP.mono (core2_ok s₂ (by rw [r2ax, r2dx]; omega_near)) fun s₃ ⟨hv₃, hm₃, k₃⟩ => ?_
  rw [r2ax, r2dx] at hv₃
  have r3_15 : s₃.gpr .r15 = s.gpr .r15 := ((k₂.trans k₃).gpr (by decide)).trans e15
  rw [WP.block_append_iff]
  refine WP.mono (core3_ok s₃ (by rw [r3_15]; omega_near)) fun s₄ ⟨hv₄, hm₄, k₄⟩ => ?_
  rw [r3_15] at hv₄
  have r4si : s₄.gpr .rsi = s.gpr .rdx := ((k₂.trans (k₃.trans k₄)).gpr (by decide)).trans hsi
  refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = s.gpr .rdx ∧ t.mem = s₄.mem)
    (by xrun [r4si]) rfl) fun t ⟨⟨hdx, hm⟩, k₅⟩ => ?_
  have K := (((k₁.trans k₂).trans k₃).trans k₄).trans k₅
  refine ⟨?_, fun r hr => ?_, hm.trans (hm₄.trans (hm₃.trans (hm₂.trans hm₁))), K.2.1, K.2.2⟩
  · rw [k₅.gpr (by decide), k₅.gpr (by decide), k₅.gpr (by decide), hv₄]
    omega_near
  · by_cases hd : r = Reg.rdx
    · subst hd; exact hdx
    · exact K.1 r (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind)

theorem core_coreOk : AdxSquare.CoreOk core := ⟨core_ok⟩

end VG.Proof.Bignum.X86_64.BaseSquare
