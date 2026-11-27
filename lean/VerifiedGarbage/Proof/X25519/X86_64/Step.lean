module

public import VerifiedGarbage.Impl.X25519.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# X25519 on x86-64: the steps of the field arithmetic

The small blocks the field operations are made of (see
`Impl/X25519/X86_64.lean`), each run symbolically once, for any registers: a
multiply-accumulate step, and the carry of a 38-fold into four words.
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

/-- The registers of `s'` are those of `s` but for `rs`, and memory and the
regions are unchanged. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keeps rs s₁ s₂) (h₂ : Keeps rs s₂ s₃) :
    Keeps rs s₁ s₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : Keeps rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Keeps rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem toNat_ofBool (c : Bool) : ((BitVec.ofBool c).setWidth 64).toNat = c.toNat := by
  cases c <;> rfl

theorem se0 : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide

/-- The arithmetic of a multiply-accumulate step: the product's halves, the
carry word `c` added to the low half, and the sum added to `t`, each carry
going into the high half, which never overflows. -/
theorem step_arith (a v c t : BitVec 64) :
    let p := a.toNat * v.toNat
    let lo : BitVec 64 := BitVec.ofNat 64 p
    let hi : BitVec 64 := BitVec.ofNat 64 (p / 2 ^ 64)
    let r := lo + c
    let d := hi + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ lo.toNat + c.toNat))).setWidth 64
    (t + r).toNat + 2 ^ 64 *
        (d + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ t.toNat + r.toNat))).setWidth 64).toNat =
      t.toNat + c.toNat + a.toNat * v.toNat := by
  intro p lo hi r d
  have ha := a.isLt; have hv := v.isLt; have hc := c.isLt; have ht := t.isLt
  have hp : p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  have hlo : lo.toNat = p % 2 ^ 64 := BitVec.toNat_ofNat _ _
  have hhi : hi.toNat = p / 2 ^ 64 := by
    simp only [hi, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega_arith)
  have hdiv : p / 2 ^ 64 ≤ 2 ^ 64 - 2 := by omega_arith
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  simp only [r, d, BitVec.toNat_add, toNat_ofBool, hz, Nat.add_zero, hlo, hhi] at *
  by_cases h1 : 2 ^ 64 ≤ p % 2 ^ 64 + c.toNat <;>
  simp only [h1, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
  [by_cases h2 : 2 ^ 64 ≤ t.toNat + (p % 2 ^ 64 + c.toNat) % 2 ^ 64;
    by_cases h2 : 2 ^ 64 ≤ t.toNat + (p % 2 ^ 64 + c.toNat) % 2 ^ 64] <;>
  simp only [h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- A multiply-accumulate step: `t:c = t + c + ai · src`. -/
theorem mulStep_ok (s : State) {t c ai : Reg} {src : Src} {v : BitVec 64}
    (hsrc : readSrc s src = some v) (ht : t ≠ .rax) (ht' : t ≠ .rdx) (hc : c ≠ .rax)
    (hc' : c ≠ .rdx) (ha : ai ≠ .rax) (htc : t ≠ c) :
    WP isa (.block (mulStep t c ai src)) s fun s' =>
      (s'.gpr t).toNat + 2 ^ 64 * (s'.gpr c).toNat =
        (s.gpr t).toNat + (s.gpr c).toNat + (s.gpr ai).toNat * v.toNat ∧
      Keeps [t, c, .rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [mulStep, runBlock_cons, reduceExec, hsrc, Option.map_some, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, execMul,
    execAlu, Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ha, hc, ht, htc, hc', ht',
    Ne.symm htc, Ne.symm ht', ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := step_arith (s.gpr ai) v (s.gpr c) (s.gpr t)
    simp only at e
    rw [Nat.mul_comm (s.gpr ai).toNat] at e ⊢
    exact e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2, ite_false]

/-- The halves of a product of two words (`mul`, `mulx`): `lo + 2⁶⁴ hi`. -/
theorem mulx_arith (d v : BitVec 64) :
    (BitVec.ofNat 64 (d.toNat * v.toNat)).toNat +
        2 ^ 64 * (BitVec.ofNat 64 (d.toNat * v.toNat / 2 ^ 64)).toNat = d.toNat * v.toNat := by
  have hd := d.isLt; have hv := v.isLt
  have hp : d.toNat * v.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hd hv
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ / 2 ^ 64) (by omega_arith)]
  omega_arith

/-! ## Carry chains -/

theorem add_carry (a b : BitVec 64) :
    (a + b).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + b.toNat)).toNat = a.toNat + b.toNat := by
  have := a.isLt; have := b.isLt
  rw [BitVec.toNat_add]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

theorem adc_carry (a b : BitVec 64) (c : Bool) :
    (a + b + (BitVec.ofBool c).setWidth 64).toNat +
        2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)).toNat =
      a.toNat + b.toNat + c.toNat := by
  have := a.isLt; have := b.isLt; have := Bool.toNat_le c
  rw [BitVec.toNat_add, BitVec.toNat_add, toNat_ofBool]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

theorem sub_borrow (a b : BitVec 64) :
    (a - b).toNat + b.toNat = a.toNat + 2 ^ 64 * (decide (a.toNat < b.toNat)).toNat := by
  have := a.isLt; have := b.isLt
  rw [BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

theorem sbb_borrow (a b : BitVec 64) (c : Bool) :
    (a - b - (BitVec.ofBool c).setWidth 64).toNat + b.toNat + c.toNat =
      a.toNat + 2 ^ 64 * (decide (a.toNat < b.toNat + c.toNat)).toNat := by
  have := a.isLt; have := b.isLt; have := Bool.toNat_le c
  rw [BitVec.toNat_sub, BitVec.toNat_sub, toNat_ofBool]
  by_cases h : a.toNat < b.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- The value of four words. -/
abbrev val4 (a0 a1 a2 a3 : BitVec 64) : Nat :=
  a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat

theorem val4_lt (a0 a1 a2 a3 : BitVec 64) : val4 a0 a1 a2 a3 < 2 ^ 256 := by
  have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt
  simp only [val4]; omega

/-- The square of four words, by the products of their words (with no
power of two above `2²⁵⁶`, which would exceed the threshold of exponents Lean evaluates). -/
theorem sq_words (x y z w : Nat) :
    (x + 2 ^ 64 * y + 2 ^ 128 * z + 2 ^ 192 * w) * (x + 2 ^ 64 * y + 2 ^ 128 * z + 2 ^ 192 * w) =
      x * x + 2 ^ 128 * (y * y) + 2 ^ 256 * (z * z) + 2 ^ 256 * (2 ^ 128 * (w * w)) +
        2 * (2 ^ 64 * (x * y) + 2 ^ 128 * (x * z) + 2 ^ 192 * (x * w) + 2 ^ 192 * (y * z) +
          2 ^ 256 * (y * w) + 2 ^ 256 * (2 ^ 64 * (z * w))) := by
  grind

/-- `add`, then three `adc`: the sum of two four-word numbers and the carry
out. -/
theorem chain_add (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    let c0 := decide (2 ^ 64 ≤ a0.toNat + b0.toNat)
    let c1 := decide (2 ^ 64 ≤ a1.toNat + b1.toNat + c0.toNat)
    let c2 := decide (2 ^ 64 ≤ a2.toNat + b2.toNat + c1.toNat)
    let c3 := decide (2 ^ 64 ≤ a3.toNat + b3.toNat + c2.toNat)
    val4 (a0 + b0) (a1 + b1 + (BitVec.ofBool c0).setWidth 64) (a2 + b2 + (BitVec.ofBool c1).setWidth 64)
        (a3 + b3 + (BitVec.ofBool c2).setWidth 64) + 2 ^ 256 * c3.toNat =
      val4 a0 a1 a2 a3 + val4 b0 b1 b2 b3 := by
  have e0 := add_carry a0 b0
  have e1 := adc_carry a1 b1 (decide (2 ^ 64 ≤ a0.toNat + b0.toNat))
  have e2 := adc_carry a2 b2 (decide (2 ^ 64 ≤ a1.toNat + b1.toNat +
    (decide (2 ^ 64 ≤ a0.toNat + b0.toNat)).toNat))
  have e3 := adc_carry a3 b3 (decide (2 ^ 64 ≤ a2.toNat + b2.toNat + (decide (2 ^ 64 ≤ a1.toNat +
    b1.toNat + (decide (2 ^ 64 ≤ a0.toNat + b0.toNat)).toNat)).toNat))
  simp only [val4]
  omega_arith

/-- `sub`, then three `sbb`: the difference of two four-word numbers, plus
`2²⁵⁶` if it borrows. -/
theorem chain_sub (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    let c0 := decide (a0.toNat < b0.toNat)
    let c1 := decide (a1.toNat < b1.toNat + c0.toNat)
    let c2 := decide (a2.toNat < b2.toNat + c1.toNat)
    let c3 := decide (a3.toNat < b3.toNat + c2.toNat)
    val4 (a0 - b0) (a1 - b1 - (BitVec.ofBool c0).setWidth 64) (a2 - b2 - (BitVec.ofBool c1).setWidth 64)
        (a3 - b3 - (BitVec.ofBool c2).setWidth 64) + val4 b0 b1 b2 b3 =
      val4 a0 a1 a2 a3 + 2 ^ 256 * c3.toNat := by
  have e0 := sub_borrow a0 b0
  have e1 := sbb_borrow a1 b1 (decide (a0.toNat < b0.toNat))
  have e2 := sbb_borrow a2 b2 (decide (a1.toNat < b1.toNat + (decide (a0.toNat < b0.toNat)).toNat))
  have e3 := sbb_borrow a3 b3 (decide (a2.toNat < b2.toNat +
    (decide (a1.toNat < b1.toNat + (decide (a0.toNat < b0.toNat)).toNat)).toNat))
  simp only [val4]
  omega_arith

/-- `sbb x, x` then `and 38`: 38 if the carry was set, else 0. -/
theorem mask38 (x : BitVec 64) (c : Bool) :
    ((x - x - (BitVec.ofBool c).setWidth 64) &&& BitVec.signExtend 64 (38 : BitVec 32)).toNat =
      38 * c.toNat := by
  cases c <;> simp only [BitVec.sub_self] <;> decide

open VG.Spec.X25519 (P) in
/-- `carry38`: `r8–r11 + rax`, with the carry out folded in as 38, is the
same number modulo `p`, if `rax < 2⁵⁸`. -/
theorem carry38_ok (s : State) (hx : (s.gpr .rax).toNat < 2 ^ 58) :
    WP isa (.block carry38) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % P =
        (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) + (s.gpr .rax).toNat) % P ∧
      Keeps [.r8, .r9, .r10, .r11, .rax] s s' := by
  apply WP.of_runBlock
  simp only [carry38, runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := chain_add (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .rax) 0 0 0
    simp only at e
    generalize hc : decide (2 ^ 64 ≤ (s.gpr Reg.r11).toNat + BitVec.toNat 0 +
      (decide (2 ^ 64 ≤ (s.gpr Reg.r10).toNat + BitVec.toNat 0 +
        (decide (2 ^ 64 ≤ (s.gpr Reg.r9).toNat + BitVec.toNat 0 +
          (decide (2 ^ 64 ≤ (s.gpr Reg.r8).toNat + (s.gpr Reg.rax).toNat)).toNat)).toNat)).toNat) = c at e ⊢
    simp only [val4] at e ⊢
    rw [BitVec.toNat_add (s.gpr .r8 + s.gpr .rax), mask38]
    have h0 := (s.gpr .r8 + s.gpr .rax).isLt
    have h1 := (s.gpr .r9).isLt; have h2 := (s.gpr .r10).isLt; have h3 := (s.gpr .r11).isLt
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    simp only [hz] at e ⊢
    have hb : (s.gpr .r8 + s.gpr .rax).toNat + 38 * c.toNat < 2 ^ 64 := by
      cases c
      · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero]; exact h0
      · simp only [Bool.toNat_true, Nat.mul_one] at e ⊢
        omega_arith
    rw [Nat.mod_eq_of_lt hb]
    have hc := Bool.toNat_le c
    simp only [P]
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

/-- `shl x, 1` then `shr x, 1`: bit 63 cleared, and shifted out into the carry. -/
theorem shl_shr_one (x : BitVec 64) :
    (x <<< 1 >>> 1).toNat + 2 ^ 63 * (x.getLsbD (64 - 1)).toNat = x.toNat ∧
      (x <<< 1 >>> 1).toNat < 2 ^ 63 := by
  have hx := x.isLt
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.reduceSub]
  by_cases h : x.toNat / 9223372036854775808 % 2 = 1 <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> constructor <;> omega_arith

/-- `adc a, a` of `a < 2⁶³` with the carry `c`: `2 a + c`. -/
theorem adcSelf_toNat (a : BitVec 64) (c : Bool) (ha : a.toNat < 2 ^ 63) :
    (a + a + (BitVec.ofBool c).setWidth 64).toNat = 2 * a.toNat + c.toNat := by
  have hc : ((BitVec.ofBool c).setWidth 64).toNat = c.toNat := by cases c <;> rfl
  have := Bool.toNat_le c
  rw [BitVec.toNat_add, BitVec.toNat_add, hc,
    Nat.mod_eq_of_lt (show a.toNat + a.toNat < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show a.toNat + a.toNat + c.toNat < 2 ^ 64 by omega_arith)]
  omega_arith

/-- `imul r, q, 19` of a small `q`: `19 q`. -/
theorem imul19_toNat (q : BitVec 64) (hq : q.toNat < 2 ^ 58) :
    (BitVec.ofInt 64 (q.toInt * ((19 : BitVec 32).signExtend 64).toInt)).toNat = 19 * q.toNat := by
  have hi : q.toInt = (q.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]; simp only [show 2 * q.toNat < 2 ^ 64 by omega_arith, ↓reduceIte]
  rw [hi, show ((19 : BitVec 32).signExtend 64).toInt = ((19 : Nat) : Int) by decide,
    ← Int.natCast_mul, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

open VG.Spec.X25519 (P) in
/-- `fold19X`: `r8–r11 + 2²⁵⁶ r12` with `r12 < 2⁵⁶`, folded into `r8–r11` at bit 255, at
most `2p`. -/
theorem fold19X_ok (s : State) (h12 : (s.gpr .r12).toNat < 2 ^ 56) :
    WP isa (.block fold19X) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % P =
        (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) + 2 ^ 256 * (s.gpr .r12).toNat) % P ∧
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) ≤ 2 * P ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .rax] s s' := by
  apply WP.of_runBlock
  simp only [fold19X, runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, execAlu,
    execShift, execImul3, Option.map_some, Option.bind_some, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    RegUpd.cf_setFlags, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left', se0,
    Nat.le_refl, and_self, Nat.reduceLeDiff]
  obtain ⟨hsh, hu⟩ := shl_shr_one (s.gpr .r11)
  generalize (s.gpr .r11).getLsbD (64 - 1) = c at hsh hu ⊢
  have hq := adcSelf_toNat (s.gpr .r12) c (by omega_arith)
  generalize s.gpr .r12 + s.gpr .r12 + (BitVec.ofBool c).setWidth 64 = q at hq ⊢
  have hc := Bool.toNat_le c
  have hr := imul19_toNat q (by omega_arith)
  generalize BitVec.ofInt 64 (q.toInt * ((19 : BitVec 32).signExtend 64).toInt) = r at hr ⊢
  generalize s.gpr .r11 <<< 1 >>> 1 = u at hsh hu ⊢
  have e := chain_add (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) u r 0 0 0
  simp only at e
  generalize decide (2 ^ 64 ≤ u.toNat + BitVec.toNat 0 + _) = c3 at e
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  have h3 := Bool.toNat_le c3
  have := (s.gpr .r8).isLt; have := (s.gpr .r9).isLt; have := (s.gpr .r10).isLt
  simp only [hz, val4] at e ⊢
  refine ⟨?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · have key : ∀ A B k : Nat, A + P * k = B → A % P = B % P := fun A B k h => by
      rw [← h, Nat.add_mul_mod_self_left]
    exact key _ _ (q.toNat) (by simp only [P]; omega_arith)
  · simp only [P]; omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hx.1, hx.2.1,
      hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2, ite_false]


/-! ## Columns of products -/

/-- The value of three words. -/
abbrev val3 (a0 a1 a2 : BitVec 64) : Nat := a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat

/-- `xor r, r`. -/
theorem zero_ok (s : State) (r : Reg) :
    WP isa (.block [zero r]) s fun s' => s'.gpr r = 0 ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [zero, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32,
    Option.bind_some, State.setReg32, RegUpd.gpr_setReg_self, BitVec.xor_self,
    Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), fun x hx => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [RegUpd.gpr_setReg_of_ne _ _ hx, RegUpd.gpr_arithFlags]

/-- The halves of a product, as `mul` leaves them. -/
theorem mul_lo_hi (x y : BitVec 64) :
    (BitVec.ofNat 64 (x.toNat * y.toNat)).toNat +
        2 ^ 64 * (BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64)).toNat = x.toNat * y.toNat ∧
      (BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64)).toNat ≤ 2 ^ 64 - 2 := by
  have hx := x.isLt; have hy := y.isLt
  have hp : x.toNat * y.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ / 2 ^ 64) (by omega_arith)]
  constructor <;> omega_arith

/-- `prod2`: the product of the word at `a` and `b` (the word itself for `b = rax`). -/
theorem prod2_ok (s : State) {t0 t1 b : Reg} {a : Nat} {v : BitVec 64}
    (hsrc : readSrc s (.mem (sc a)) = some v) (h01 : t0 ≠ t1) (h0d : t0 ≠ .rdx) :
    WP isa (.block (prod2 t0 t1 b a)) s fun s' =>
      (s'.gpr t0).toNat + 2 ^ 64 * (s'.gpr t1).toNat =
        v.toNat * (if b = .rax then v else s.gpr b).toNat ∧
      Keeps [t0, t1, .rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [prod2, runBlock_cons, reduceExec, hsrc, Option.map_some, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, execMul,
    Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, h01,
    Ne.symm h01, h0d, Ne.symm h0d, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · exact (mul_lo_hi _ _).1
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- `acc2`: a product added to two words, and the carry out. -/
theorem acc2_ok (s : State) {t0 t1 b : Reg} {a : Nat} {v : BitVec 64}
    (hsrc : readSrc s (.mem (sc a)) = some v) (h01 : t0 ≠ t1) (h0a : t0 ≠ .rax) (h0d : t0 ≠ .rdx)
    (h1a : t1 ≠ .rax) (h1d : t1 ≠ .rdx) (hb : b ≠ .rax) :
    WP isa (.block (acc2 t0 t1 b a)) s fun s' =>
      (∃ c : Bool, (s'.gpr t0).toNat + 2 ^ 64 * (s'.gpr t1).toNat + 2 ^ 128 * c.toNat =
        (s.gpr t0).toNat + 2 ^ 64 * (s.gpr t1).toNat + v.toNat * (s.gpr b).toNat) ∧
      Keeps [t0, t1, .rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [acc2, runBlock_cons, reduceExec, hsrc, Option.map_some, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, execMul, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, h01, Ne.symm h01,
    h0a, h0d, h1a, h1d, hb, Ne.symm h0d, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left']
  obtain ⟨hm, -⟩ := mul_lo_hi v (s.gpr b)
  have e0 := add_carry (s.gpr t0) (BitVec.ofNat 64 (v.toNat * (s.gpr b).toNat))
  have e1 := adc_carry (s.gpr t1) (BitVec.ofNat 64 (v.toNat * (s.gpr b).toNat / 2 ^ 64))
    (decide (2 ^ 64 ≤ (s.gpr t0).toNat + (BitVec.ofNat 64 (v.toNat * (s.gpr b).toNat)).toNat))
  generalize decide (2 ^ 64 ≤ (s.gpr t0).toNat + _) = c0 at e0 e1 ⊢
  generalize decide (2 ^ 64 ≤ (s.gpr t1).toNat + _ + c0.toNat) = c1 at e1 ⊢
  refine ⟨⟨c1, ?_⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  · omega_using [hm, e0, e1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2, ite_false]

/-- `acc3`: a product added to the three words of a column, whose highest
word, which counts the carries, does not overflow. -/
theorem acc3_ok (s : State) {t0 t1 t2 b : Reg} {a : Nat} {v : BitVec 64}
    (hsrc : readSrc s (.mem (sc a)) = some v)
    (hd : ([t0, t1, t2, .rax, .rdx] : List Reg).Nodup) (hb : b ≠ .rax)
    (h2 : (s.gpr t2).toNat + 1 < 2 ^ 64) :
    WP isa (.block (acc3 t0 t1 t2 b a)) s fun s' =>
      val3 (s'.gpr t0) (s'.gpr t1) (s'.gpr t2) =
        val3 (s.gpr t0) (s.gpr t1) (s.gpr t2) + v.toNat * (s.gpr b).toNat ∧
      (s'.gpr t2).toNat ≤ (s.gpr t2).toNat + 1 ∧
      Keeps [t0, t1, t2, .rax, .rdx] s s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h0a, h0d⟩, ⟨h12, h1a, h1d⟩, ⟨h2a, h2d⟩, -⟩ := hd
  apply WP.of_runBlock
  simp only [acc3, acc2, List.cons_append, List.nil_append, runBlock_cons, reduceExec, hsrc,
    Option.map_some, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, execMul, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, h01, Ne.symm h01,
    h02, Ne.symm h02, h12, Ne.symm h12, h0a, h0d, h1a, h1d, h2a, h2d, hb, Ne.symm h0d,
    ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left', se0]
  obtain ⟨hm, -⟩ := mul_lo_hi v (s.gpr b)
  have e0 := add_carry (s.gpr t0) (BitVec.ofNat 64 (v.toNat * (s.gpr b).toNat))
  have e1 := adc_carry (s.gpr t1) (BitVec.ofNat 64 (v.toNat * (s.gpr b).toNat / 2 ^ 64))
    (decide (2 ^ 64 ≤ (s.gpr t0).toNat + (BitVec.ofNat 64 (v.toNat * (s.gpr b).toNat)).toNat))
  generalize decide (2 ^ 64 ≤ (s.gpr t0).toNat + _) = c0 at e0 e1 ⊢
  generalize decide (2 ^ 64 ≤ (s.gpr t1).toNat + _ + c0.toNat) = c1 at e1 ⊢
  have e2 := adc_carry (s.gpr t2) 0 c1
  have hc1 := Bool.toNat_le c1
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  rw [hz, Nat.add_zero, show decide (2 ^ 64 ≤ (s.gpr t2).toNat + c1.toNat) = false from
    decide_eq_false (by omega_arith), Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at e2
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [val3]; omega_using [hm, e0, e1, e2]
  · omega_using [e2, hc1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- `r8–r12` doubled, for `r12 < 2⁶³`. -/
theorem dbl5_ok (s : State) (h12 : (s.gpr .r12).toNat < 2 ^ 63) :
    WP isa (.block dbl5) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + 2 ^ 256 * (s'.gpr .r12).toNat =
        2 * (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          2 ^ 256 * (s.gpr .r12).toNat) ∧
      (s'.gpr .r12).toNat ≤ 2 * (s.gpr .r12).toNat + 1 ∧
      Keeps [.r8, .r9, .r10, .r11, .r12] s s' := by
  apply WP.of_runBlock
  simp only [dbl5, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left']
  have e8 := add_carry (s.gpr .r8) (s.gpr .r8)
  generalize decide (2 ^ 64 ≤ (s.gpr .r8).toNat + (s.gpr .r8).toNat) = c8 at e8 ⊢
  have e9 := adc_carry (s.gpr .r9) (s.gpr .r9) c8
  generalize decide (2 ^ 64 ≤ (s.gpr .r9).toNat + (s.gpr .r9).toNat + c8.toNat) = c9 at e9 ⊢
  have e10 := adc_carry (s.gpr .r10) (s.gpr .r10) c9
  generalize decide (2 ^ 64 ≤ (s.gpr .r10).toNat + (s.gpr .r10).toNat + c9.toNat) = c10 at e10 ⊢
  have e11 := adc_carry (s.gpr .r11) (s.gpr .r11) c10
  generalize decide (2 ^ 64 ≤ (s.gpr .r11).toNat + (s.gpr .r11).toNat + c10.toNat) = c11 at e11 ⊢
  have e12 := adc_carry (s.gpr .r12) (s.gpr .r12) c11
  generalize decide (2 ^ 64 ≤ (s.gpr .r12).toNat + (s.gpr .r12).toNat + c11.toNat) = c12 at e12 ⊢
  have := Bool.toNat_le c8; have := Bool.toNat_le c9; have := Bool.toNat_le c10
  have := Bool.toNat_le c11; have := Bool.toNat_le c12
  refine ⟨?_, ?_, fun r hr => ?_, by trivial, by trivial, by trivial⟩
  · simp only [val4]; omega_using [h12, e8, e9, e10, e11, e12]
  · omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]


end VG.Proof.X25519.X86_64
