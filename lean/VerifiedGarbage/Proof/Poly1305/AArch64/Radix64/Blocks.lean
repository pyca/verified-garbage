import VerifiedGarbage.Impl.Poly1305.AArch64.Radix64
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Poly1305.AArch64.Init
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Lit

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Steps`. -/
section

/-! Instruction-level proofs for the radix-64 Poly1305 arithmetic. -/
namespace VG.Proof.Poly1305.AArch64.Radix64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Poly1305.AArch64.Radix64
open VG.Proof.Poly1305.Limbs64

def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.gpr' {rs : List Reg} {s s' : State} (h : VG.Proof.Poly1305.AArch64.Radix64.Keeps rs s s') {r : Reg}
    (hr : r ∉ rs := by decide) : s'.gpr r = s.gpr r := h.1 r hr

theorem Keeps.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Poly1305.AArch64.Radix64.Keeps rs s₁ s₂)
    (h₂ : VG.Proof.Poly1305.AArch64.Radix64.Keeps rs' s₂ s₃) : VG.Proof.Poly1305.AArch64.Radix64.Keeps (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1],
   h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : VG.Proof.Poly1305.AArch64.Radix64.Keeps rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : VG.Proof.Poly1305.AArch64.Radix64.Keeps rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

/-- The carry bit embedded in a word is target-independent. -/
theorem ofNat_bool (c : Bool) : BitVec.ofNat 64 c.toNat = (BitVec.ofBool c).setWidth 64 := by
  cases c <;> rfl

theorem threeimm : (3#16).setWidth 64 = 3#64 := by decide

theorem zero_nat : (0#64).toNat = 0 := rfl

theorem mul_words (a b : BitVec 64) :
    (a * b).toNat + 2 ^ 64 * (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat =
      a.toNat * b.toNat := by
  simpa only [BitVec.toNat_mul, BitVec.toNat_ofNat] using toNat_mul_lo a b

set_option simprocs false in
theorem mulTo_ok {lo hi a b : Reg} (s : State) (ha : a ≠ lo) (hb : b ≠ lo)
    (hlh : lo ≠ hi) :
    WP isa (.block (mulTo lo hi a b)) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat = (s.gpr a).toNat * (s.gpr b).toNat ∧
      VG.Proof.Poly1305.AArch64.Radix64.Keeps [lo, hi] s s' := by
  apply WP.of_runBlock
  simp only [mulTo, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    BitVec.setWidth_eq, gpr_write, ha, hb, hlh,
    ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨VG.Proof.Poly1305.AArch64.Radix64.mul_words _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [gpr_write, hr.1, hr.2, ite_false]

set_option simprocs false in
theorem mulAdd_ok {lo hi a b : Reg} (s : State) (ha : a ≠ .x13) (hb : b ≠ .x13)
    (hl0 : lo ≠ .x13) (hl1 : lo ≠ .x14) (hh0 : hi ≠ .x13) (hh1 : hi ≠ .x14)
    (hlh : hi ≠ lo) :
    WP isa (.block (mulAdd lo hi a b)) s fun s' =>
      ((s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat + (s.gpr a).toNat * (s.gpr b).toNat < 2 ^ 128 →
        (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat =
          (s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat + (s.gpr a).toNat * (s.gpr b).toNat) ∧
      VG.Proof.Poly1305.AArch64.Radix64.Keeps [lo, hi, .x13, .x14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mulAdd, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, gpr_write, gpr_addWithCarry, c_addWithCarry,
    ha, hb, hl0, hl1, hh0, hh1, hlh, hlh.symm, hl1.symm,
    ite_true, ite_false, Bool.toNat_false, Nat.add_zero, BitVec.add_zero,
    Option.some.injEq, exists_eq_left', VG.Proof.Poly1305.AArch64.Radix64.ofNat_bool]
  refine ⟨fun hlt => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := VG.Proof.Poly1305.AArch64.Radix64.mul_words (s.gpr a) (s.gpr b)
    rw [add_adc_toNat _ _ _ _ (by omega_using [hlt, e])]
    omega_using [e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]


abbrev hval (s : State) : Nat :=
  (s.gpr .x4).toNat + 2 ^ 64 * (s.gpr .x5).toNat + 2 ^ 128 * (s.gpr .x6).toNat

abbrev word (m : Mem) (p : Addr) (d : Nat) : Nat := (m.readW (p + BitVec.ofNat 64 d) 64).toNat

set_option simprocs false in
theorem mulAddSmall_ok (s : State) :
    WP isa (.block (mulAddSmall .x11 .x12 .x6 .x17)) s fun s' =>
      ((s.gpr .x6).toNat * (s.gpr .x17).toNat < 2 ^ 64 →
        (s.gpr .x11).toNat + 2 ^ 64 * (s.gpr .x12).toNat +
          (s.gpr .x6).toNat * (s.gpr .x17).toNat < 2 ^ 128 →
        (s'.gpr .x11).toNat + 2 ^ 64 * (s'.gpr .x12).toNat =
          (s.gpr .x11).toNat + 2 ^ 64 * (s.gpr .x12).toNat +
            (s.gpr .x6).toNat * (s.gpr .x17).toNat) ∧ VG.Proof.Poly1305.AArch64.Radix64.Keeps [.x11, .x12, .x13, .x14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mulAddSmall, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, gpr_write, gpr_addWithCarry, c_addWithCarry,
    ite_true, ite_false, Bool.toNat_false, Nat.add_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.setWidth_zero,
    Option.some.injEq, exists_eq_left', VG.Proof.Poly1305.AArch64.Radix64.ofNat_bool]
  refine ⟨fun hp hlt => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e : (s.gpr .x6 * s.gpr .x17).toNat = (s.gpr .x6).toNat * (s.gpr .x17).toNat := by
      rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hp]
    have h := add_adc_toNat (s.gpr .x11) (s.gpr .x6 * s.gpr .x17) (s.gpr .x12) 0
      (by simp only [e, BitVec.ofNat_eq_ofNat, VG.Proof.Poly1305.AArch64.Radix64.zero_nat, Nat.add_zero]; omega_using [hlt])
    simp only [e, BitVec.ofNat_eq_ofNat, VG.Proof.Poly1305.AArch64.Radix64.zero_nat, Nat.add_zero, BitVec.add_zero] at h
    rw [e]
    omega_using [h]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

set_option simprocs false in
theorem mulSmall_ok (s : State) :
    WP isa (.block [.mul .x .x13 .x6 .x7]) s fun s' =>
      ((s.gpr .x6).toNat * (s.gpr .x7).toNat < 2 ^ 64 →
        (s'.gpr .x13).toNat = (s.gpr .x6).toNat * (s.gpr .x7).toNat) ∧ VG.Proof.Poly1305.AArch64.Radix64.Keeps [.x13] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    BitVec.setWidth_eq, gpr_write_self, Option.some.injEq, exists_eq_left']
  refine ⟨fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]
  · simp only [List.mem_singleton] at hr
    exact gpr_write_of_ne _ _ _ hr

set_option simprocs false in
theorem combine_ok (s : State) :
    WP isa (.block combine) s fun s' =>
      ((s.gpr .x11).toNat + (s.gpr .x10).toNat +
          2 ^ 64 * ((s.gpr .x12).toNat + (s.gpr .x13).toNat) < 2 ^ 128 →
        (s'.gpr .x11).toNat + 2 ^ 64 * (s'.gpr .x12).toNat =
          (s.gpr .x11).toNat + (s.gpr .x10).toNat +
            2 ^ 64 * ((s.gpr .x12).toNat + (s.gpr .x13).toNat)) ∧ VG.Proof.Poly1305.AArch64.Radix64.Keeps [.x11, .x12] s s' := by
  apply WP.of_runBlock
  simp only [combine, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, gpr_write, gpr_addWithCarry, c_addWithCarry,
    ite_true, Bool.toNat_false, Nat.add_zero, BitVec.add_zero,
    Option.some.injEq, exists_eq_left', VG.Proof.Poly1305.AArch64.Radix64.ofNat_bool]
  refine ⟨add_adc_toNat _ _ _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2, ite_false]

set_option simprocs false in
theorem fold_ok (s : State) :
    WP isa (.block fold) s fun s' =>
      s'.gpr .x4 = s.gpr .x9 ∧ s'.gpr .x5 = s.gpr .x11 ∧
      (s'.gpr .x6).toNat = (s.gpr .x12).toNat % 4 ∧
      ((s.gpr .x12).toNat < 2 ^ 63 → (s'.gpr .x13).toNat = 5 * ((s.gpr .x12).toNat / 4)) ∧
      VG.Proof.Poly1305.AArch64.Radix64.Keeps [.x4, .x5, .x6, .x12, .x13, .x14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [fold, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, gpr_write, ite_true, ite_false,
    Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    BitVec.shiftLeft_zero, VG.Proof.Poly1305.AArch64.Radix64.threeimm, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, and3_toNat _, fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h3 := and3_toNat (s.gpr .x12)
    simp only [BitVec.ofNat_eq_ofNat] at h3
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h3]
    omega_using [h]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

set_option simprocs false in
theorem addLow_ok (s : State) :
    WP isa (.block addLow) s fun s' =>
      (VG.Proof.Poly1305.AArch64.Radix64.hval s + (s.gpr .x13).toNat < 2 ^ 192 → VG.Proof.Poly1305.AArch64.Radix64.hval s' = VG.Proof.Poly1305.AArch64.Radix64.hval s + (s.gpr .x13).toNat) ∧
      VG.Proof.Poly1305.AArch64.Radix64.Keeps [.x4, .x5, .x6, .x14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addLow, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, VG.Proof.Poly1305.AArch64.Radix64.hval, gpr_write, gpr_addWithCarry, c_addWithCarry,
    ite_true, ite_false, Bool.toNat_false, Nat.add_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.setWidth_zero,
    Option.some.injEq, exists_eq_left', VG.Proof.Poly1305.AArch64.Radix64.ofNat_bool]
  refine ⟨fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := add3_toNat (s.gpr .x4) (s.gpr .x13) (s.gpr .x5) 0 (s.gpr .x6) 0
      (by simp only [BitVec.ofNat_eq_ofNat, VG.Proof.Poly1305.AArch64.Radix64.zero_nat, Nat.add_zero]; omega_using [h])
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, VG.Proof.Poly1305.AArch64.Radix64.zero_nat, Nat.add_zero] at e
    simp only [VG.Proof.Poly1305.AArch64.Radix64.zero_nat, Nat.add_zero]
    omega_using [e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]


theorem pad_word (pad : Bool) :
    ((if pad then (1 : BitVec 16) else 0).setWidth 64) = BitVec.ofNat 64 pad.toNat := by
  cases pad <;> rfl

set_option simprocs false in
theorem addBlock_ok (s : State) (pad : Bool)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 0) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 8) 8) :
    WP isa (.block (addBlock pad)) s fun s' =>
      (VG.Proof.Poly1305.AArch64.Radix64.hval s + (VG.Proof.Poly1305.AArch64.Radix64.word s.mem (s.gpr .x1) 0 + 2 ^ 64 * VG.Proof.Poly1305.AArch64.Radix64.word s.mem (s.gpr .x1) 8 +
          2 ^ 128 * pad.toNat) < 2 ^ 192 →
        VG.Proof.Poly1305.AArch64.Radix64.hval s' = VG.Proof.Poly1305.AArch64.Radix64.hval s + (VG.Proof.Poly1305.AArch64.Radix64.word s.mem (s.gpr .x1) 0 +
          2 ^ 64 * VG.Proof.Poly1305.AArch64.Radix64.word s.mem (s.gpr .x1) 8 + 2 ^ 128 * pad.toNat)) ∧
      VG.Proof.Poly1305.AArch64.Radix64.Keeps [.x4, .x5, .x6, .x13, .x14, .x15] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addBlock, runBlock_cons, runStep_some,
    exec_ldr_x (show 0 % 8 = 0 ∧ 0 < 32768 by decide) h0,
    exec_ldr_x (show 8 % 8 = 0 ∧ 8 < 32768 by decide),
    gpr_write, mem_write, rd_write, wr_write, h8, ite_false]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, VG.Proof.Poly1305.AArch64.Radix64.hval, gpr_write,
    gpr_addWithCarry, c_addWithCarry, ite_true, ite_false, Bool.toNat_false,
    Nat.add_zero, BitVec.add_zero, Nat.mul_zero,
    BitVec.shiftLeft_zero, Option.some.injEq, exists_eq_left', VG.Proof.Poly1305.AArch64.Radix64.pad_word, VG.Proof.Poly1305.AArch64.Radix64.ofNat_bool]
  refine ⟨fun hlt => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have hp : ((BitVec.ofBool pad).setWidth 64).toNat = pad.toNat := carry_toNat pad
    have e := add3_toNat (s.gpr .x4) (s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 0) 64)
      (s.gpr .x5) (s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 8) 64)
      (s.gpr .x6) ((BitVec.ofBool pad).setWidth 64)
      (by simp only [hp]; simp only [VG.Proof.Poly1305.AArch64.Radix64.word] at hlt; omega_using [hlt])
    rw [hp] at e
    simp only [BitVec.add_zero] at e
    simp only [VG.Proof.Poly1305.AArch64.Radix64.word, BitVec.add_zero]
    omega_using [e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

end VG.Proof.Poly1305.AArch64.Radix64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Absorb`. -/
section

namespace VG.Proof.Poly1305.AArch64.Radix64
open VG VG.AArch64 VG.Impl.Poly1305.AArch64.Radix64
open VG.Proof.Poly1305.Limbs64
open VG.Spec.Poly1305 (P)

abbrev absorbRegs : List Reg := [.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x15]

theorem absorb_eq (pad : Bool) : absorb pad =
    addBlock pad ++ (mulTo .x9 .x10 .x4 .x7 ++ (mulAdd .x9 .x10 .x5 .x17 ++
    (mulTo .x11 .x12 .x4 .x8 ++ (mulAdd .x11 .x12 .x5 .x7 ++
    (mulAddSmall .x11 .x12 .x6 .x17 ++ (([.mul .x .x13 .x6 .x7] : List Instr) ++
    (combine ++ (fold ++ addLow)))))))) := by
  simp only [absorb, products, List.append_assoc]

/-- `products ++ combine ++ fold ++ addLow`: `x4:x5:x6` (`x6 ≤ 6`) times the key, partially reduced. -/
theorem mul_eq : Impl.Poly1305.AArch64.Radix64.products ++ combine ++ fold ++ addLow =
    mulTo .x9 .x10 .x4 .x7 ++ (mulAdd .x9 .x10 .x5 .x17 ++
    (mulTo .x11 .x12 .x4 .x8 ++ (mulAdd .x11 .x12 .x5 .x7 ++
    (mulAddSmall .x11 .x12 .x6 .x17 ++ (([.mul .x .x13 .x6 .x7] : List Instr) ++
    (combine ++ (fold ++ addLow))))))) := by
  simp only [Impl.Poly1305.AArch64.Radix64.products, List.append_assoc]

theorem mul_ok (s₁ : State) {q : Nat}
    (hr0 : (s₁.gpr .x7).toNat < 2 ^ 60) (hr1 : (s₁.gpr .x8).toNat = 4 * q) (hq : q < 2 ^ 58)
    (hs1 : (s₁.gpr .x17).toNat = 5 * q) :
    WP isa (.block (Impl.Poly1305.AArch64.Radix64.products ++ combine ++ fold ++ addLow)) s₁ fun s' =>
      ((s₁.gpr .x6).toNat ≤ 6 →
        VG.Proof.Poly1305.AArch64.Radix64.hval s' % P = (VG.Proof.Poly1305.AArch64.Radix64.hval s₁ * ((s₁.gpr .x7).toNat + 2 ^ 64 * (s₁.gpr .x8).toNat)) % P ∧
        (s'.gpr .x6).toNat ≤ 4) ∧ VG.Proof.Poly1305.AArch64.Radix64.Keeps VG.Proof.Poly1305.AArch64.Radix64.absorbRegs s₁ s' := by
  rw [VG.Proof.Poly1305.AArch64.Radix64.mul_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.AArch64.Radix64.mulTo_ok s₁ (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.AArch64.Radix64.mulAdd_ok s₂ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₃ ⟨e₃, k₃⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.AArch64.Radix64.mulTo_ok s₃ (by decide) (by decide) (by decide))
    fun s₄ ⟨e₄, k₄⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.AArch64.Radix64.mulAdd_ok s₄ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₅ ⟨e₅, k₅⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.AArch64.Radix64.mulAddSmall_ok s₅) fun s₆ ⟨e₆, k₆⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.AArch64.Radix64.mulSmall_ok s₆) fun s₇ ⟨e₇, k₇⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.AArch64.Radix64.combine_ok s₇) fun s₈ ⟨e₈, k₈⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.AArch64.Radix64.fold_ok s₈) fun s₉ ⟨f₁, f₂, f₃, f₄, k₉⟩ => ?_)
  refine WP.mono (VG.Proof.Poly1305.AArch64.Radix64.addLow_ok s₉) fun s₁₀ ⟨e₁₀, k₁₀⟩ => ?_
  refine ⟨fun a2 => ?_, (((((((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans
    k₈).trans k₉).trans k₁₀)).mono (by decide)⟩
  have a0 := (s₁.gpr .x4).isLt; have a1 := (s₁.gpr .x5).isLt
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := absorb_bounds a0 a1 a2 hr0 hq
  -- x = h0 r0
  have rbx₂ : s₂.gpr .x5 = s₁.gpr .x5 := k₂.gpr'
  have r10₂ : s₂.gpr .x17 = s₁.gpr .x17 := k₂.gpr'
  -- x += h1 s1
  rw [rbx₂, r10₂, hs1] at e₃
  have e₃ := e₃ (by omega_using [e₂, b1, b2])
  rw [e₂] at e₃
  have k₃' := k₂.trans k₃
  have r11₃ : s₃.gpr .x4 = s₁.gpr .x4 := k₃'.gpr'
  have r9₃ : s₃.gpr .x8 = s₁.gpr .x8 := k₃'.gpr'
  -- y = h0 r1
  rw [r11₃, r9₃, hr1] at e₄
  have k₄' := k₃'.trans k₄
  have rbx₄ : s₄.gpr .x5 = s₁.gpr .x5 := k₄'.gpr'
  have r8₄ : s₄.gpr .x7 = s₁.gpr .x7 := k₄'.gpr'
  -- y += h1 r0
  rw [rbx₄, r8₄] at e₅
  have e₅ := e₅ (by omega_using [e₄, b3, b4])
  rw [e₄] at e₅
  have k₅' := k₄'.trans k₅
  have rbp₅ : s₅.gpr .x6 = s₁.gpr .x6 := k₅'.gpr'
  have r10₅ : s₅.gpr .x17 = s₁.gpr .x17 := k₅'.gpr'
  -- y += h2 s1
  rw [rbp₅, r10₅, hs1] at e₆
  have e₆ := e₆ b5 (by omega_using [e₄, b3, b4, b5, e₅])
  rw [e₅] at e₆
  have k₆' := k₅'.trans k₆
  have rbp₆ : s₆.gpr .x6 = s₁.gpr .x6 := k₆'.gpr'
  have r8₆ : s₆.gpr .x7 = s₁.gpr .x7 := k₆'.gpr'
  -- h2 r0
  rw [rbp₆, r8₆] at e₇
  have e₇ := e₇ (by omega_using [hr0, b6])
  have r14₇ : s₇.gpr .x11 = s₆.gpr .x11 := k₇.gpr'
  have r15₇ : s₇.gpr .x12 = s₆.gpr .x12 := k₇.gpr'
  have r13₇ : s₇.gpr .x10 = s₃.gpr .x10 := ((k₄.trans k₅).trans (k₆.trans k₇)).gpr'
  have r12₇ : s₇.gpr .x9 = s₃.gpr .x9 := ((k₄.trans k₅).trans (k₆.trans k₇)).gpr'
  have x0 := (s₃.gpr .x9).isLt; have x1 := (s₃.gpr .x10).isLt
  have y0 := (s₆.gpr .x11).isLt; have y1 := (s₆.gpr .x12).isLt
  -- the top word
  rw [r14₇, r13₇, r15₇, e₇] at e₈
  have e₈ := e₈ (by omega_using [hr0, e₂, e₄, b1, b2, b3, b4, b5, b6, e₃, e₅, e₆, e₇])
  have u0 := (s₈.gpr .x11).isLt
  have ht : (s₈.gpr .x12).toNat < 2 ^ 63 := by omega_using [hr0, e₂, e₄, b1, b2, b3, b4, b5, b6, e₃, e₅, e₆, e₇, e₈]
  have f₄ := f₄ ht
  have r12₈ : s₈.gpr .x9 = s₃.gpr .x9 := k₈.gpr'.trans r12₇
  rw [r12₈] at f₁
  dsimp only [VG.Proof.Poly1305.AArch64.Radix64.hval] at e₁₀
  rw [f₁, f₂, f₃, f₄] at e₁₀
  have e₁₀ := e₁₀ (by omega_using [hr0, e₂, e₄, b1, b2, b3, b4, b5, b6, e₃, e₅, e₆, e₇, e₈])
  have w0 := (s₁₀.gpr .x4).isLt; have w1 := (s₁₀.gpr .x5).isLt
  have hu : (s₈.gpr .x11).toNat + 2 ^ 64 * (((s₆.gpr .x11).toNat + (s₃.gpr .x10).toNat) / 2 ^ 64) =
      (s₆.gpr .x11).toNat + (s₃.gpr .x10).toNat := by
    clear e₁₀ f₁ f₂ f₃ f₄ e₃ e₆ e₇
    omega_using [e₈]
  have ht' : (s₈.gpr .x12).toNat = (s₆.gpr .x12).toNat + (s₁.gpr .x6).toNat * (s₁.gpr .x7).toNat +
      ((s₆.gpr .x11).toNat + (s₃.gpr .x10).toNat) / 2 ^ 64 := by
    clear e₁₀ f₁ f₂ f₃ f₄ e₃ e₆ e₇
    omega_using [e₈, hu]
  rw [ht'] at e₁₀
  obtain ⟨m, hb⟩ := absorb_arith (q := q)
    (w0 := (s₁₀.gpr .x4).toNat) (w1 := (s₁₀.gpr .x5).toNat) (w2 := (s₁₀.gpr .x6).toNat) (x0 := (s₃.gpr .x9).toNat) (x1 := (s₃.gpr .x10).toNat)
    (y0 := (s₆.gpr .x11).toNat) (y1 := (s₆.gpr .x12).toNat) (u0 := (s₈.gpr .x11).toNat)
    (c1 := ((s₆.gpr .x11).toNat + (s₃.gpr .x10).toNat) / 2 ^ 64)
    a0 a1 a2 hr0 hq e₃ x0 e₆ hu u0 (by omega_using [e₁₀]) w0 w1
  refine ⟨?_, hb⟩
  rw [VG.Proof.Poly1305.AArch64.Radix64.hval, m]
  change (VG.Proof.Poly1305.AArch64.Radix64.hval s₁ * _) % P = _
  rw [hr1]

theorem absorb_ok (s : State) (pad : Bool) {q : Nat}
    (hr0 : (s.gpr .x7).toNat < 2 ^ 60) (hr1 : (s.gpr .x8).toNat = 4 * q) (hq : q < 2 ^ 58)
    (hs1 : (s.gpr .x17).toNat = 5 * q)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 0) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 8) 8) :
    WP isa (.block (absorb pad)) s fun s' =>
      ((s.gpr .x6).toNat ≤ 4 →
        VG.Proof.Poly1305.AArch64.Radix64.hval s' % P = ((VG.Proof.Poly1305.AArch64.Radix64.hval s + (VG.Proof.Poly1305.AArch64.Radix64.word s.mem (s.gpr .x1) 0 + 2 ^ 64 * VG.Proof.Poly1305.AArch64.Radix64.word s.mem (s.gpr .x1) 8 +
          2 ^ 128 * pad.toNat)) * ((s.gpr .x7).toNat + 2 ^ 64 * (s.gpr .x8).toNat)) % P ∧
        (s'.gpr .x6).toNat ≤ 4) ∧ VG.Proof.Poly1305.AArch64.Radix64.Keeps VG.Proof.Poly1305.AArch64.Radix64.absorbRegs s s' := by
  rw [show absorb pad = addBlock pad ++ (Impl.Poly1305.AArch64.Radix64.products ++ combine ++ fold ++ addLow) by
    simp only [absorb, List.append_assoc]]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.AArch64.Radix64.addBlock_ok s pad h0 h8) fun s₁ ⟨e₁, k₁⟩ => ?_)
  have r8₁ : s₁.gpr .x7 = s.gpr .x7 := k₁.gpr'
  have r9₁ : s₁.gpr .x8 = s.gpr .x8 := k₁.gpr'
  have r10₁ : s₁.gpr .x17 = s.gpr .x17 := k₁.gpr'
  refine WP.mono (VG.Proof.Poly1305.AArch64.Radix64.mul_ok s₁ (by rw [r8₁]; exact hr0) (by rw [r9₁]; exact hr1) hq (by rw [r10₁]; exact hs1))
    fun s' ⟨hm, k⟩ => ⟨fun hh2 => ?_, (k₁.trans k).mono (by decide)⟩
  have hp1 : pad.toNat ≤ 1 := Bool.toNat_le pad
  have hw0 := (s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 0) 64).isLt
  have hw8 := (s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 8) 64).isLt
  have g0 := (s.gpr .x4).isLt; have g1 := (s.gpr .x5).isLt
  have e₁ := e₁ (by simp only [VG.Proof.Poly1305.AArch64.Radix64.word, VG.Proof.Poly1305.AArch64.Radix64.hval]; omega_using [hh2, hp1, hw0, hw8, g0, g1])
  have a0 := (s₁.gpr .x4).isLt; have a1 := (s₁.gpr .x5).isLt
  obtain ⟨hv, hb⟩ := hm (add_arith g0 g1 hh2 hw0 hw8 hp1 e₁ a0 a1)
  refine ⟨?_, hb⟩
  rw [hv, e₁, r8₁, r9₁]

end VG.Proof.Poly1305.AArch64.Radix64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Reduce`. -/
section

namespace VG.Proof.Poly1305.AArch64.Radix64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Poly1305.AArch64.Radix64
open VG.Proof.Poly1305.Limbs64
open VG.Spec.Poly1305 (P)

theorem select_zero (x y : BitVec 64) : x ^^^ ((y ^^^ x) &&& ((0 : BitVec 64) - 0)) = x := by
  simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_self, BitVec.and_zero, BitVec.xor_zero]

theorem select_one (x y : BitVec 64) : x ^^^ ((y ^^^ x) &&& ((0 : BitVec 64) - 1)) = y := by
  rw [show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes, BitVec.xor_comm y,
    ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem fiveimm : (5#16).setWidth 64 = 5#64 := by decide

theorem reduce_eq : reduce = plus5 ++ (mask ++
    (selectLimb .x4 .x9 ++ selectLimb .x5 .x10 ++ selectLimb .x6 .x11)) := by
  simp only [reduce, List.append_assoc]

set_option simprocs false in
theorem plus5_ok (s : State) :
    WP isa (.block plus5) s fun s' =>
      (VG.Proof.Poly1305.AArch64.Radix64.hval s + 5 < 2 ^ 192 →
        (s'.gpr .x9).toNat + 2 ^ 64 * (s'.gpr .x10).toNat + 2 ^ 128 * (s'.gpr .x11).toNat =
          VG.Proof.Poly1305.AArch64.Radix64.hval s + 5) ∧ VG.Proof.Poly1305.AArch64.Radix64.Keeps [.x9, .x10, .x11, .x13, .x14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [plus5, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, gpr_write, gpr_addWithCarry, c_addWithCarry,
    ite_true, ite_false, Bool.toNat_false, Nat.add_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.setWidth_zero, VG.Proof.Poly1305.AArch64.Radix64.fiveimm,
    Option.some.injEq, exists_eq_left', VG.Proof.Poly1305.AArch64.Radix64.ofNat_bool]
  refine ⟨fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := add3_toNat (s.gpr .x4) 5 (s.gpr .x5) 0 (s.gpr .x6) 0
      (by change (s.gpr .x4).toNat + 5 + 2 ^ 64 * ((s.gpr .x5).toNat + 0) +
          2 ^ 128 * ((s.gpr .x6).toNat + 0) < _
          simp only [VG.Proof.Poly1305.AArch64.Radix64.hval] at h; omega_using [h])
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, VG.Proof.Poly1305.AArch64.Radix64.zero_nat, Nat.add_zero] at e
    change _ = (s.gpr .x4).toNat + 2 ^ 64 * (s.gpr .x5).toNat + 2 ^ 128 * (s.gpr .x6).toNat + 5
    simp only [VG.Proof.Poly1305.AArch64.Radix64.zero_nat, Nat.add_zero]
    have h5 : (5#64).toNat = 5 := rfl
    simp only [h5] at e ⊢
    omega_using [e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

set_option simprocs false in
theorem mask_ok (s : State) :
    WP isa (.block mask) s fun s' =>
      s'.gpr .x12 = (0 : BitVec 64) - (s.gpr .x11 >>> 2) ∧
      s'.gpr .x11 = s.gpr .x11 &&& 3 ∧ VG.Proof.Poly1305.AArch64.Radix64.Keeps [.x11, .x12, .x14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mask, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, gpr_write, ite_true, ite_false,
    Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, BitVec.setWidth_zero, VG.Proof.Poly1305.AArch64.Radix64.threeimm,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

set_option simprocs false in
theorem select_ok (s : State) :
    WP isa (.block (selectLimb .x4 .x9 ++ selectLimb .x5 .x10 ++ selectLimb .x6 .x11)) s fun s' =>
      s'.gpr .x4 = s.gpr .x4 ^^^ ((s.gpr .x9 ^^^ s.gpr .x4) &&& s.gpr .x12) ∧
      s'.gpr .x5 = s.gpr .x5 ^^^ ((s.gpr .x10 ^^^ s.gpr .x5) &&& s.gpr .x12) ∧
      s'.gpr .x6 = s.gpr .x6 ^^^ ((s.gpr .x11 ^^^ s.gpr .x6) &&& s.gpr .x12) ∧
      VG.Proof.Poly1305.AArch64.Radix64.Keeps [.x4, .x5, .x6, .x13] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [selectLimb, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, BitVec.setWidth_eq,
    gpr_write, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem reduce_ok (s : State) :
    WP isa (.block reduce) s fun s' =>
      ((s.gpr .x6).toNat ≤ 4 → VG.Proof.Poly1305.AArch64.Radix64.hval s' = VG.Proof.Poly1305.AArch64.Radix64.hval s % P) ∧
      VG.Proof.Poly1305.AArch64.Radix64.Keeps [.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14] s s' := by
  have g0 := (s.gpr .x4).isLt; have g1 := (s.gpr .x5).isLt
  rw [VG.Proof.Poly1305.AArch64.Radix64.reduce_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.AArch64.Radix64.plus5_ok s) fun s₁ ⟨e₁, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.AArch64.Radix64.mask_ok s₁) fun s₂ ⟨m₁, m₂, k₂⟩ => ?_)
  refine WP.mono (VG.Proof.Poly1305.AArch64.Radix64.select_ok s₂) fun s₃ ⟨c₁, c₂, c₃, k₃⟩ => ?_
  refine ⟨fun hh2 => ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  have e₁ := e₁ (by simp only [VG.Proof.Poly1305.AArch64.Radix64.hval]; omega_using [g0, g1, hh2])
  have ga := (s₁.gpr .x9).isLt; have gd := (s₁.gpr .x10).isLt
  have hg2 : (s₁.gpr .x11).toNat ≤ 5 := by simp only [VG.Proof.Poly1305.AArch64.Radix64.hval] at e₁; omega_using [g0, g1, hh2, e₁]
  have r11₂ : s₂.gpr .x4 = s.gpr .x4 := (k₁.trans k₂).gpr'
  have rbx₂ : s₂.gpr .x5 = s.gpr .x5 := (k₁.trans k₂).gpr'
  have rbp₂ : s₂.gpr .x6 = s.gpr .x6 := (k₁.trans k₂).gpr'
  have rax₂ : s₂.gpr .x9 = s₁.gpr .x9 := k₂.gpr'
  have rdx₂ : s₂.gpr .x10 = s₁.gpr .x10 := k₂.gpr'
  rw [r11₂, rax₂, m₁] at c₁; rw [rbx₂, rdx₂, m₁] at c₂; rw [rbp₂, m₂, m₁] at c₃
  have ht : (s₁.gpr .x11 >>> 2).toNat = (s₁.gpr .x11).toNat / 4 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [VG.Proof.Poly1305.AArch64.Radix64.hval, c₁, c₂, c₃]
  unfold VG.Proof.Poly1305.AArch64.Radix64.hval at e₁
  have hP : P = 2 ^ 130 - 5 := rfl
  by_cases hge : 4 ≤ (s₁.gpr .x11).toNat
  · have h1 : s₁.gpr .x11 >>> 2 = 1 := BitVec.eq_of_toNat_eq (by rw [ht]; simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.one_mod]; omega_using [hg2, ht, hge])
    rw [h1, VG.Proof.Poly1305.AArch64.Radix64.select_one, VG.Proof.Poly1305.AArch64.Radix64.select_one, VG.Proof.Poly1305.AArch64.Radix64.select_one, and3_toNat]
    have ge : P ≤ (s.gpr .x4).toNat + 2 ^ 64 * (s.gpr .x5).toNat + 2 ^ 128 * (s.gpr .x6).toNat := by
      omega_using [e₁, hg2, hP, hge]
    have lt : (s.gpr .x4).toNat + 2 ^ 64 * (s.gpr .x5).toNat + 2 ^ 128 * (s.gpr .x6).toNat - P <
        P := by omega_using [g0, g1, hh2, e₁, hP, ge]
    rw [Nat.mod_eq_sub_mod ge, Nat.mod_eq_of_lt lt]
    omega_using [g0, g1, hh2, e₁, hP, ge, lt]
  · have h0 : s₁.gpr .x11 >>> 2 = 0 := BitVec.eq_of_toNat_eq (by rw [ht]; simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.div_eq_zero_iff, reduceCtorEq, false_or]; omega_using [hg2, hge])
    have lt : (s.gpr .x4).toNat + 2 ^ 64 * (s.gpr .x5).toNat + 2 ^ 128 * (s.gpr .x6).toNat <
        P := by omega_using [e₁, hg2, hP, hge]
    rw [h0, VG.Proof.Poly1305.AArch64.Radix64.select_zero, VG.Proof.Poly1305.AArch64.Radix64.select_zero, VG.Proof.Poly1305.AArch64.Radix64.select_zero, Nat.mod_eq_of_lt lt]


end VG.Proof.Poly1305.AArch64.Radix64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Setup`. -/
section

namespace VG.Proof.Poly1305.AArch64.Radix64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64.Radix64
open VG.Proof.Poly1305.AArch64
open VG.Spec.Poly1305 (P)

def Keys (R : Nat) (s : State) : Prop :=
  ∃ q, (s.gpr .x7).toNat < 2 ^ 60 ∧ (s.gpr .x8).toNat = 4 * q ∧ q < 2 ^ 58 ∧
    (s.gpr .x17).toNat = 5 * q ∧ (s.gpr .x7).toNat + 2 ^ 64 * (s.gpr .x8).toNat = R

def Bounds (s : State) : Prop := (s.gpr .x6).toNat ≤ 4

abbrev hv := VG.Proof.Poly1305.AArch64.Radix64.hval

theorem key0_lt (k : BitVec 64) : (k &&& M0).toNat < 2 ^ 60 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem key1_lt (k : BitVec 64) : (k &&& M1).toNat < 2 ^ 60 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem key1_mod (k : BitVec 64) : (k &&& M1).toNat % 4 = 0 := by
  rw [BitVec.toNat_and, show (4 : Nat) = 2 ^ 2 from rfl,
    ← Nat.and_two_pow_sub_one_eq_mod, Nat.and_assoc,
    show M1.toNat &&& 2 ^ 2 - 1 = 0 by decide, Nat.and_zero]

theorem s1_toNat (k : BitVec 64) :
    (((k &&& M1) >>> 2) + (k &&& M1)).toNat = 5 * ((k &&& M1).toNat / 4) := by
  have h1 := VG.Proof.Poly1305.AArch64.Radix64.key1_lt k
  have h2 := VG.Proof.Poly1305.AArch64.Radix64.key1_mod k
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega_using [h1, h2]

set_option simprocs false in
theorem setup_regs (s : State) (hw : sR (s.gpr .x0) ∈ s.rd ++ s.wr) :
    WP isa (.block setup) s fun s' =>
      s'.gpr .x7 = s.mem.readW (off (s.gpr .x0) 24) 64 &&& M0 ∧
      s'.gpr .x8 = s.mem.readW (off (s.gpr .x0) 32) 64 &&& M1 ∧
      (s'.gpr .x17).toNat = 5 * ((s'.gpr .x8).toNat / 4) ∧
      s'.gpr .x4 = s.mem.readW (off (s.gpr .x0) 0) 64 ∧
      s'.gpr .x5 = s.mem.readW (off (s.gpr .x0) 8) 64 ∧
      s'.gpr .x6 = s.mem.readW (off (s.gpr .x0) 16) 64 ∧
      VG.Proof.Poly1305.AArch64.Radix64.Keeps [.x4, .x5, .x6, .x7, .x8, .x16, .x17] s s' := by
  have i : ∀ d, d + 8 ≤ 128 →
      InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨_, hw, contains_off hd (by omega_using [hd])⟩
  have i0 := i 0 (by decide)
  have i8 := i 8 (by decide)
  have i16 := i 16 (by decide)
  have i24 := i 24 (by decide)
  have i32 := i 32 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [setup, VG.Impl.Poly1305.AArch64.const64,
    List.cons_append, List.nil_append, runBlock_cons, runBlock_nil, isa, runStep_some,
    exec, addr, Size.bytes, State.load, i0, i8, i16, i24, i32, State.read, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [movz_movk64']; rfl
  · rw [movz_movk64']; rfl
  · rw [movz_movk64', VG.Proof.Poly1305.AArch64.Radix64.s1_toNat]
  · rfl
  · rfl
  · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

theorem setup_ok (s : State) (hw : sR (s.gpr .x0) ∈ s.wr) :
    WP isa (.block setup) s fun s' =>
      VG.Proof.Poly1305.AArch64.Radix64.Keys (Rk s.mem (s.gpr .x0)) s' ∧
      (A0 s < P → VG.Proof.Poly1305.AArch64.Radix64.hval s' = A0 s ∧ VG.Proof.Poly1305.AArch64.Radix64.Bounds s') ∧
      VG.Proof.Poly1305.AArch64.Radix64.Keeps [.x4, .x5, .x6, .x7, .x8, .x16, .x17] s s' := by
  refine (VG.Proof.Poly1305.AArch64.Radix64.setup_regs s (List.mem_append_right _ hw)).mono fun s' ⟨r0, r1, t, h0, h1, h2, k⟩ => ?_
  refine ⟨?_, ?_, k⟩
  · refine ⟨(s'.gpr .x8).toNat / 4, ?_, ?_, ?_, t, ?_⟩
    · rw [r0]; exact VG.Proof.Poly1305.AArch64.Radix64.key0_lt _
    · have e := VG.Proof.Poly1305.AArch64.Radix64.key1_mod (s.mem.readW (off (s.gpr .x0) 32) 64)
      rw [← r1] at e
      omega_using [e]
    · have e := VG.Proof.Poly1305.AArch64.Radix64.key1_lt (s.mem.readW (off (s.gpr .x0) 32) 64)
      rw [← r1] at e
      omega_using [e]
    · rw [r0, r1]
  · intro hA
    have e : VG.Proof.Poly1305.AArch64.Radix64.hval s' = A0 s := by
      simp only [VG.Proof.Poly1305.AArch64.Radix64.hval, h0, h1, h2, A0, leNum_acc, w64, off]
    refine ⟨e, ?_⟩
    have a0 := (s'.gpr .x4).isLt
    have a1 := (s'.gpr .x5).isLt
    simp only [VG.Proof.Poly1305.AArch64.Radix64.Bounds, VG.Proof.Poly1305.AArch64.Radix64.hval, P] at e hA ⊢
    omega_using [e, hA, a0, a1]

theorem Keys.of_regs {R : Nat} {s s' : State} (hk : VG.Proof.Poly1305.AArch64.Radix64.Keys R s)
    (h : ∀ r ∈ [Reg.x7, .x8, .x17], s'.gpr r = s.gpr r) : VG.Proof.Poly1305.AArch64.Radix64.Keys R s' := by
  simpa only [VG.Proof.Poly1305.AArch64.Radix64.Keys, h .x7 (by simp), h .x8 (by simp), h .x17 (by simp)] using hk

theorem bounds_eq {s s' : State}
    (h : ∀ r ∈ [Reg.x4, .x5, .x6], s'.gpr r = s.gpr r) :
    VG.Proof.Poly1305.AArch64.Radix64.hval s' = VG.Proof.Poly1305.AArch64.Radix64.hval s ∧ (VG.Proof.Poly1305.AArch64.Radix64.Bounds s → VG.Proof.Poly1305.AArch64.Radix64.Bounds s') := by
  simp only [VG.Proof.Poly1305.AArch64.Radix64.hval, VG.Proof.Poly1305.AArch64.Radix64.Bounds, h .x4 (by simp), h .x5 (by simp), h .x6 (by simp)]
  exact ⟨trivial, id⟩

theorem absorb_key_ok (s : State) (pad : Bool) {R : Nat} (hk : VG.Proof.Poly1305.AArch64.Radix64.Keys R s)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 0) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 8) 8) :
    WP isa (.block (absorb pad)) s fun s' =>
      (VG.Proof.Poly1305.AArch64.Radix64.Bounds s → VG.Proof.Poly1305.AArch64.Radix64.hval s' % P =
        ((VG.Proof.Poly1305.AArch64.Radix64.hval s + (VG.Proof.Poly1305.AArch64.Radix64.word s.mem (s.gpr .x1) 0 + 2 ^ 64 * VG.Proof.Poly1305.AArch64.Radix64.word s.mem (s.gpr .x1) 8 +
          2 ^ 128 * pad.toNat)) * R) % P ∧ VG.Proof.Poly1305.AArch64.Radix64.Bounds s') ∧ VG.Proof.Poly1305.AArch64.Radix64.Keeps VG.Proof.Poly1305.AArch64.Radix64.absorbRegs s s' := by
  obtain ⟨q, hr0, hr1, hq, hs1, hr⟩ := hk
  simpa only [← hr, VG.Proof.Poly1305.AArch64.Radix64.Bounds] using VG.Proof.Poly1305.AArch64.Radix64.absorb_ok s pad hr0 hr1 hq hs1 h0 h8

end VG.Proof.Poly1305.AArch64.Radix64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.AddS`. -/
section

namespace VG.Proof.Poly1305.AArch64.Radix64
open VG VG.AArch64 VG.Impl.Poly1305.AArch64.Radix64
open VG.Proof.Poly1305.AArch64 VG.Proof.Poly1305.Limbs64

theorem add_adc_mod (a b c d : BitVec 64) :
    (a + b).toNat + 2 ^ 64 *
      (c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64).toNat =
      (a.toNat + b.toNat + 2 ^ 64 * (c.toNat + d.toNat)) % 2 ^ 128 := by
  have h1 := addc0 a b
  have h2 := addc1 c d (decide (2 ^ 64 ≤ a.toNat + b.toNat))
  have lo := (a + b).isLt
  have hi := (c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64).isLt
  omega_using [h1, h2, lo, hi]

set_option simprocs false in
theorem addS_ok (s : State) (hw : sR (s.gpr .x0) ∈ s.wr) :
    WP isa (.block addS) s fun s' =>
      (s'.gpr .x4).toNat + 2 ^ 64 * (s'.gpr .x5).toNat =
        ((s.gpr .x4).toNat + 2 ^ 64 * (s.gpr .x5).toNat +
          (s.mem.readW (off (s.gpr .x0) 40) 64).toNat +
          2 ^ 64 * (s.mem.readW (off (s.gpr .x0) 48) 64).toNat) % 2 ^ 128 ∧
      VG.Proof.Poly1305.AArch64.Radix64.Keeps [.x4, .x5, .x13, .x14] s s' := by
  have i : ∀ d, d + 8 ≤ 128 →
      InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, contains_off hd (by omega_using [hd])⟩
  have i40 := i 40 (by decide); have i48 := i 48 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addS, runBlock_cons, runBlock_nil, isa, runStep_some,
    exec, addr, Size.bytes, State.load, i40, i48, State.read, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    ite_true, ite_false, Bool.toNat_false, Nat.add_zero, BitVec.add_zero,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', VG.Proof.Poly1305.AArch64.Radix64.ofNat_bool]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [VG.Proof.Poly1305.AArch64.Radix64.add_adc_mod]
    congr 1
    change (s.gpr .x4).toNat + (s.mem.readW (off (s.gpr .x0) 40) 64).toNat +
      2 ^ 64 * ((s.gpr .x5).toNat + (s.mem.readW (off (s.gpr .x0) 48) 64).toNat) =
      (s.gpr .x4).toNat + 2 ^ 64 * (s.gpr .x5).toNat +
      (s.mem.readW (off (s.gpr .x0) 40) 64).toNat +
      2 ^ 64 * (s.mem.readW (off (s.gpr .x0) 48) 64).toNat
    omega_using []
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2, ite_false]

end VG.Proof.Poly1305.AArch64.Radix64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Blocks`. -/
section

namespace VG.Proof.Poly1305.AArch64.Radix64
open VG VG.AArch64 VG.Impl.Poly1305.AArch64.Radix64
open VG.Proof.Poly1305.AArch64
open VG.Spec.Poly1305 (P bytesAt leNum clamp accumulate Repr)

structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  keys : VG.Proof.Poly1305.AArch64.Radix64.Keys (Rn s₀) s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = s₀.mem
  acc : A0 s₀ < P → VG.Proof.Poly1305.AArch64.Radix64.hval s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (blks s₀ i) % P ∧ VG.Proof.Poly1305.AArch64.Radix64.Bounds s

structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends VG.Proof.Poly1305.AArch64.Radix64.Common s₀ i s where
  x1 : s.gpr .x1 = blkAddr s₀ i
  x2 : s.gpr .x2 = BitVec.ofNat 64 (nb s₀ - i)

def body : Prog isa := .block (absorb true ++ VG.Impl.Poly1305.AArch64.advance)

theorem body_ok {s₀ : State} (hp : BPre s₀) {i : Nat}
    (hi : i < nb s₀) {s : State} (hL : VG.Proof.Poly1305.AArch64.Radix64.LInv s₀ i s) :
    WP isa VG.Proof.Poly1305.AArch64.Radix64.body s fun s' =>
      (eval (.nonzero .x .x2) s' = some false ∧ VG.Proof.Poly1305.AArch64.Radix64.Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .x .x2) s' = some true ∧ i + 1 < nb s₀ ∧ VG.Proof.Poly1305.AArch64.Radix64.LInv s₀ (i + 1) s') := by
  have hin : ∀ d : Nat, d + 8 ≤ 16 →
      InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [hL.rd, hL.wr, hL.x1, hp.rd]
    exact ⟨blR s₀, List.mem_append_left _ (List.mem_singleton_self _), hp.blk_contains hi hd⟩
  have hab := VG.Proof.Poly1305.AArch64.Radix64.absorb_key_ok s true hL.keys (hin 0 (by decide)) (hin 8 (by decide))
  change WP isa (.block (absorb true ++ VG.Impl.Poly1305.AArch64.advance)) s _
  refine WP.block_append (WP.mono hab fun s₁ ⟨ha, k₁⟩ => ?_)
  refine WP.mono (VG.Proof.Poly1305.AArch64.advance_ok s₁) fun s₂ ⟨a₁, a₂, k₂⟩ => ?_
  have k₂ : VG.Proof.Poly1305.AArch64.Radix64.Keeps [.x1, .x2] s₁ s₂ := k₂
  have k := k₁.trans k₂
  have hc : VG.Proof.Poly1305.AArch64.Radix64.Common s₀ (i + 1) s₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, fun hA => ?_⟩
    · rw [k.gpr' (r := .x0), hL.x0]
    · exact hL.keys.of_regs fun r hr => k.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide)
    · rw [k.2.2.1, hL.rd]
    · rw [k.2.2.2, hL.wr]
    · rw [k.2.1, hL.mem]
    · obtain ⟨hv₀, hb⟩ := hL.acc hA
      obtain ⟨hv', hb'⟩ := ha hb
      obtain ⟨e₂, b₂⟩ := VG.Proof.Poly1305.AArch64.Radix64.bounds_eq (s := s₁) (s' := s₂) fun r hr => k₂.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl <;> decide)
      refine ⟨?_, b₂ hb'⟩
      have h16 : (blks s₀ i).length % 16 = 0 := by
        simp only [blks, Poly1305.length_bytesAt]; omega_using []
      have hb1 : 0 < (bytesAt s₀.mem (blkAddr s₀ i) 16).length := by
        rw [Poly1305.length_bytesAt]; omega_using []
      have hb2 : (bytesAt s₀.mem (blkAddr s₀ i) 16).length ≤ 16 := by rw [Poly1305.length_bytesAt]
      rw [e₂, hv', hL.x1, hL.mem, show VG.Proof.Poly1305.AArch64.Radix64.word s₀.mem (blkAddr s₀ i) 0 = w64 s₀.mem (blkAddr s₀ i) 0 from rfl, show VG.Proof.Poly1305.AArch64.Radix64.word s₀.mem (blkAddr s₀ i) 8 = w64 s₀.mem (blkAddr s₀ i) 8 from rfl, VG.Proof.Poly1305.AArch64.block_value hp (Frame.refl _ _) hi, mod_step hv₀, blks_succ,
        Poly1305.absorbAll_append h16, Poly1305.absorbAll_block hb1 hb2]
  have hx2 : s₂.gpr .x2 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [a₂, k₁.gpr' (r := .x2), hL.x2, Offset.ofNat_sub_ofNat (by omega_using [hi]), Nat.sub_sub]
  have hev : eval (.nonzero .x .x2) s₂ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hx2]
  have := hp.nb_lt
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp only [Nat.sub_self, BitVec.ofNat_eq_ofNat, bne_self_eq_false], hlast ▸ hc⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega_using [hi, hlast]
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, this, h'])] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega_using [hi, hne], { hc with x1 := ?_, x2 := hx2 }⟩
    rw [a₁, k₁.gpr' (r := .x1), hL.x1, blkAddr, blkAddr, Offset.add_add, Nat.mul_succ]


set_option simprocs false in
theorem storeH_ok (s : State) (hw : sR (s.gpr .x0) ∈ s.wr) :
    WP isa (.block storeH) s fun s' =>
      s'.mem = storeHm s.mem (s.gpr .x0) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .x0) d) 8 :=
    fun d hd => ⟨_, hw, contains_off hd (by omega_using [hd])⟩
  have o0 := o 0 (by decide); have o8 := o 8 (by decide); have o16 := o 16 (by decide)
  simp only [off] at o0 o8 o16
  apply WP.of_runBlock
  simp only [and_self, storeH, runBlock_cons, runStep_some, runBlock_nil,
    exec_str_x (show 0 % 8 = 0 ∧ 0 < 32768 by decide) o0, exec_str_x (show 8 % 8 = 0 ∧ 8 < 32768 by decide),
    exec_str_x (show 16 % 8 = 0 ∧ 16 < 32768 by decide), o8, o16, Option.some.injEq, exists_eq_left']
  trivial

theorem epilogue_ok {s₀ : State} (hp : BPre s₀) {s : State}
    (hc : VG.Proof.Poly1305.AArch64.Radix64.Common s₀ (nb s₀) s) :
    WP isa (.block (reduce ++ storeH)) s fun s' => Proof.Poly1305.blocksAArch64.post s₀ s' := by
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.AArch64.Radix64.reduce_ok s) fun s₁ ⟨hr, k₁⟩ => ?_)
  have x0₁ : s₁.gpr .x0 = st s₀ := by rw [k₁.gpr', hc.x0]
  refine WP.mono (VG.Proof.Poly1305.AArch64.Radix64.storeH_ok s₁ (by
    rw [k₁.2.2.2, hc.wr, hp.wr, x0₁]; exact List.mem_singleton_self _))
    fun s₂ ⟨m₂, _, _, _⟩ => ?_
  intro key msg hrep
  have hA := A0_lt hrep
  obtain ⟨hv₀, hb⟩ := hc.acc hA
  have hN := hr hb
  have mem₁ : s₁.mem = s₀.mem := by rw [k₁.2.1, hc.mem]
  rw [x0₁, mem₁] at m₂
  have hf : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₂.mem := by
    rw [m₂]; exact storeHm_frame (Frame.refl _ _) _ _ _
  have hlen := hrep.1
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_append, Poly1305.length_bytesAt]; omega_using [hlen]
  · rw [← off_24, key_frame hf]; exact repr_key hrep
  · rw [m₂, storeHm_acc, ← repr_key hrep, clamp_key, Poly1305.accumulate_append hlen, repr_acc hrep]
    change VG.Proof.Poly1305.AArch64.Radix64.hval s₁ = _
    rw [hN, hv₀, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)]

theorem blocks_correct {s₀ : State} (hp : BPre s₀) :
    WP isa blocks s₀ (Proof.Poly1305.blocksAArch64.post s₀) := by
  rw [blocks]
  refine WP.seq (WP.mono (VG.Proof.Poly1305.AArch64.Radix64.setup_ok s₀ (by rw [hp.wr]; exact List.mem_singleton_self _))
    fun s₁ h₁ => ?_)
  obtain ⟨hk, ha, k⟩ := h₁
  have hc₀ : VG.Proof.Poly1305.AArch64.Radix64.Common s₀ 0 s₁ := ⟨k.gpr' (r := .x0), hk, k.2.2.1, k.2.2.2, k.2.1,
    fun hA => by
      obtain ⟨e, b⟩ := ha hA
      refine ⟨?_, b⟩
      rw [e, show blks s₀ 0 = [] by simp only [blks, bytesAt, Nat.mul_zero, List.range_zero, List.map_nil], Poly1305.absorbAll_nil]⟩
  have x2₁ : s₁.gpr .x2 = s₀.gpr .x2 := k.gpr' (r := .x2)
  refine WP.seq (WP.mono (Q := VG.Proof.Poly1305.AArch64.Radix64.Common s₀ (nb s₀)) ?_ fun s₂ hc₂ => VG.Proof.Poly1305.AArch64.Radix64.epilogue_ok hp hc₂)
  refine WP.ite (s₁.read .x .x2 == 0) rfl (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by
      simp only [State.read, Size.bits, BitVec.setWidth_eq, x2₁, beq_iff_eq] at h
      simp only [nb, h, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [State.read, Size.bits, BitVec.setWidth_eq, x2₁, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ VG.Proof.Poly1305.AArch64.Radix64.LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa VG.Proof.Poly1305.AArch64.Radix64.body s (fun s' =>
        (eval (.nonzero .x .x2) s' = some false ∧ VG.Proof.Poly1305.AArch64.Radix64.Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .x .x2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (VG.Proof.Poly1305.AArch64.Radix64.body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega_using [hi'], i + 1, rfl, hi', hL'⟩
    have hL₀ : VG.Proof.Poly1305.AArch64.Radix64.LInv s₀ 0 s₁ :=
      { hc₀ with
        x1 := by rw [k.gpr' (r := .x1)]; simp only [blkAddr, Nat.mul_zero, BitVec.add_zero]
        x2 := by rw [x2₁]; simp only [nb, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

theorem blocks_untouched : Untouched Impl.Poly1305.AArch64.Radix64.blocks :=
  Untouched.of_all (by rw [← Code.allInstrs_eq]; lit_decide)

theorem blocks_ok (s : State) (hs : Proof.Poly1305.blocksAArch64.pre s) :
    ∃ t s', Exec isa Impl.Poly1305.AArch64.Radix64.blocks s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.blocksAArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.Poly1305.AArch64.Radix64.blocks_correct (BPre.of s hs)
  exact ⟨t, s', he, ⟨fun r hr => Exec.gpr (VG.Proof.Poly1305.AArch64.Radix64.blocks_untouched r hr) he, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h⟩

theorem blocks_ct : ConstantTime isa Proof.Poly1305.blocksAArch64.pre
    Proof.Poly1305.blocksAArch64.pub Impl.Poly1305.AArch64.Radix64.blocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

theorem blocks_verified :
    Verified AArch64.target Impl.Poly1305.AArch64.Radix64.blocks (Spec.Poly1305.blocksContract AArch64.abi)
      :=
  Verified.of_correct VG.Proof.Poly1305.AArch64.Radix64.blocks_ok VG.Proof.Poly1305.AArch64.Radix64.blocks_ct (by
    sig_implies [Spec.Poly1305.blocksContract, Spec.Poly1305.blocksSig,
      Proof.Poly1305.blocksAArch64, AArch64.abi, AArch64.argRegs] [Proof.Poly1305.AArch64.blocksSat]
      using Proof.Poly1305.AArch64.blocksSat)

end VG.Proof.Poly1305.AArch64.Radix64

end
