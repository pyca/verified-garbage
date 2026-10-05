import VerifiedGarbage.Impl.Ed25519.X86_64.MulAdd
import VerifiedGarbage.Proof.X25519.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Impl.Ed25519.X86_64.Scalar
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.ScalarStep`. -/
section

/-!
# Ed25519 scalar reduction: the conditional subtraction on x86-64

Borrow equations account for every bit of all four limbs. The masked selection
implements the conditional subtraction of `L`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (val4 Keeps adc_carry chain_sub se0 toNat_ofBool mask xor_sel)
open VG.Spec.Ed25519 (L)

def scalarValue (s : State) : Nat := val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11)
def savedValue (s : State) : Nat := val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15)

theorem val4_bound (a b c d : BitVec 64) : val4 a b c d < 2 ^ 256 := by
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [val4]; omega

theorem order_limbs : val4 orderLo orderHi 0 orderTop = L := by decide

theorem subtract_chain (a b c d : BitVec 64) :
    let c0 := decide (a.toNat < orderLo.toNat)
    let c1 := decide (b.toNat < orderHi.toNat + c0.toNat)
    let c2 := decide (c.toNat < (0 : BitVec 64).toNat + c1.toNat)
    let c3 := decide (d.toNat < orderTop.toNat + c2.toNat)
    let v := val4 (a - orderLo) (b - orderHi - (BitVec.ofBool c0).setWidth 64)
      (c - 0 - (BitVec.ofBool c1).setWidth 64) (d - orderTop - (BitVec.ofBool c2).setWidth 64)
    c3 = decide (val4 a b c d < L) ∧
      v + L = val4 a b c d + 2 ^ 256 * c3.toNat := by
  intro c0 c1 c2 c3 v
  have e := chain_sub a b c d orderLo orderHi 0 orderTop
  change v + val4 orderLo orderHi 0 orderTop = val4 a b c d + 2 ^ 256 * c3.toNat at e
  rw [VG.Proof.Ed25519.X86_64.order_limbs] at e
  have hv : v < 2 ^ 256 := VG.Proof.Ed25519.X86_64.val4_bound _ _ _ _
  have hx := VG.Proof.Ed25519.X86_64.val4_bound a b c d
  clear_value v c3 c2 c1 c0
  refine ⟨?_, e⟩
  cases c3 <;> simp only [Bool.toNat_false, Bool.toNat_true] at e
  · exact (decide_eq_false (by omega)).symm
  · exact (decide_eq_true (by omega)).symm

theorem scalarSubtract_ok (s : State) :
    WP isa (.block scalarSubtract) s fun t =>
      t.cf = some (decide (VG.Proof.Ed25519.X86_64.scalarValue s < L)) ∧
      VG.Proof.Ed25519.X86_64.scalarValue t + L = VG.Proof.Ed25519.X86_64.scalarValue s + 2 ^ 256 * (decide (VG.Proof.Ed25519.X86_64.scalarValue s < L)).toNat ∧
      VG.Proof.Ed25519.X86_64.savedValue t = VG.Proof.Ed25519.X86_64.scalarValue s ∧
      Keeps [.rcx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  apply WP.of_runBlock
  simp only [scalarSubtract, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', se0]
  obtain ⟨hc, he⟩ := VG.Proof.Ed25519.X86_64.subtract_chain (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11)
  simp only [VG.Proof.Ed25519.X86_64.scalarValue, VG.Proof.Ed25519.X86_64.savedValue, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg,
    ite_true, ite_false, reduceCtorEq]
  refine ⟨hc, ?_, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [hc] at he; exact he
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem sbb_mask (x : BitVec 64) (b : Bool) :
    x - x - (BitVec.ofBool b).setWidth 64 = mask b := by
  rw [BitVec.sub_self]
  cases b <;> decide

theorem scalarSelect_ok (s : State) (borrow : Bool) (hc : s.cf = some borrow) :
    WP isa (.block scalarSelect) s fun t =>
      VG.Proof.Ed25519.X86_64.scalarValue t = (if borrow then VG.Proof.Ed25519.X86_64.savedValue s else VG.Proof.Ed25519.X86_64.scalarValue s) ∧
      Keeps [.rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  apply WP.of_runBlock
  simp only [scalarSelect, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hc,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', VG.Proof.Ed25519.X86_64.sbb_mask]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [VG.Proof.Ed25519.X86_64.scalarValue, VG.Proof.Ed25519.X86_64.savedValue, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
      ite_true, ite_false, reduceCtorEq, (xor_sel borrow _ _).2]
    cases borrow <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

def scalarClob : List Reg := [.rax, .rcx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem select_remainder (x y : Nat) (hx : x < 2 * L)
    (he : y + L = x + 2 ^ 256 * (decide (x < L)).toNat) :
    (if x < L then x else y) = x % L := by
  by_cases h : x < L
  · rw [ite_eq_left h, Nat.mod_eq_of_lt h]
  · simp only [h, decide_false, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at he
    rw [ite_eq_right h, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.ScalarWord`. -/
section

/-!
# Ed25519 scalar reduction: one word on x86-64

`wordFold` turns the remainder `r < L` and the next word `w` into `l + L - h
c` for `2^64 r + w = h 2^252 + l`, with `L = 2^252 + c`: below `2L` and
congruent to `2^64 r + w` modulo `L` (`fold_nat`). Each of its blocks is
checked against the numbers it computes.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (val4 Keeps adc_carry add_carry sub_borrow sbb_borrow mulx_arith se0 toNat_ofBool
  chain_add chain_sub)
open VG.Spec.Ed25519 (L)

/-! ## Numbers -/

/-- `L - 2^252`. -/
def cL : Nat := 27742317777372353535851937790883648493

theorem L_eq : L = 2 ^ 252 + VG.Proof.Ed25519.X86_64.cL := by decide

theorem c_limbs : orderLo.toNat + 2 ^ 64 * orderHi.toNat = VG.Proof.Ed25519.X86_64.cL := by decide

/-- One word folded in: `l + L - h c` is below `2L` and congruent to `v = 2^64 r + w`. -/
theorem fold_nat (r w : Nat) (hr : r < L) (hw : w < 2 ^ 64) :
    (r * 2 ^ 64 + w) / 2 ^ 252 * VG.Proof.Ed25519.X86_64.cL < L ∧
    (r * 2 ^ 64 + w) % 2 ^ 252 + (L - (r * 2 ^ 64 + w) / 2 ^ 252 * VG.Proof.Ed25519.X86_64.cL) < 2 * L ∧
    ((r * 2 ^ 64 + w) % 2 ^ 252 + (L - (r * 2 ^ 64 + w) / 2 ^ 252 * VG.Proof.Ed25519.X86_64.cL)) % L = (r * 2 ^ 64 + w) % L := by
  rw [VG.Proof.Ed25519.X86_64.L_eq] at hr ⊢
  generalize hv : r * 2 ^ 64 + w = v
  have hv' : v < 2 ^ 317 := by rw [← hv]; simp only [VG.Proof.Ed25519.X86_64.cL] at hr; omega
  have hh : v / 2 ^ 252 < 2 ^ 65 := by omega
  have hc : v / 2 ^ 252 * VG.Proof.Ed25519.X86_64.cL < 2 ^ 65 * VG.Proof.Ed25519.X86_64.cL := Nat.mul_lt_mul_of_pos_right hh (by decide)
  have hd := Nat.div_add_mod v (2 ^ 252)
  simp only [VG.Proof.Ed25519.X86_64.cL] at hc ⊢
  refine ⟨by omega, by omega, ?_⟩
  generalize v / 2 ^ 252 = h at hc hd
  generalize v % 2 ^ 252 = l at hd ⊢
  subst hd
  have e : l + (2 ^ 252 + 27742317777372353535851937790883648493 - h * 27742317777372353535851937790883648493) +
      h * (2 ^ 252 + 27742317777372353535851937790883648493) =
      2 ^ 252 * h + l + (2 ^ 252 + 27742317777372353535851937790883648493) := by
    rw [Nat.mul_add]; omega
  rw [← Nat.add_mul_mod_self_right _ h, e, Nat.add_mod_right]

/-! ## The blocks -/

theorem or_mul16 {a b : Nat} (h : a < 2 ^ 4) : a ||| 16 * b = a + 16 * b := by
  rw [show 16 * b = b * 2 ^ 4 by omega, Nat.or_comm, ← Nat.shiftLeft_eq,
    ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq, Nat.add_comm]

theorem sixteen (x : BitVec 64) :
    (x + x + (x + x) + (x + x + (x + x)) + (x + x + (x + x) + (x + x + (x + x)))).toNat =
      16 * (x.toNat % 2 ^ 60) := by
  have := x.isLt
  simp only [BitVec.toNat_add]
  omega

theorem foldPrep_ok (s : State) :
    WP isa (.block foldPrep) s fun t =>
      (t.gpr .rbp).toNat = (s.gpr .r10).toNat / 2 ^ 60 + 16 * ((s.gpr .r11).toNat % 2 ^ 60) ∧
      (t.gpr .r12).toNat = (s.gpr .r11).toNat / 2 ^ 60 ∧
      t.gpr .r8 = s.gpr .rax ∧ t.gpr .r9 = s.gpr .r8 ∧ t.gpr .r10 = s.gpr .r9 ∧
      (t.gpr .r11).toNat = (s.gpr .r10).toNat % 2 ^ 60 ∧
      Keeps [.rbp, .rcx, .r8, .r9, .r10, .r11, .r12] s t := by
  apply WP.of_runBlock
  simp only [foldPrep, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execShift,
    execAlu, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    show 1 ≤ 60 ∧ 60 ≤ 63 by decide, and_self, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, trivial, trivial, trivial, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_or, VG.Proof.Ed25519.X86_64.sixteen, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact VG.Proof.Ed25519.X86_64.or_mul16 (by have := (s.gpr .r10).isLt; omega)
  · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · rw [BitVec.toNat_and, show (1152921504606846975 : BitVec 64).toNat = 2 ^ 60 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

theorem foldMul_ok (s : State) :
    WP isa (.block foldMul) s fun t =>
      (t.gpr .r13).toNat + 2 ^ 64 * (t.gpr .r14).toNat + 2 ^ 128 * (t.gpr .r15).toNat =
        (s.gpr .rbp).toNat * VG.Proof.Ed25519.X86_64.cL ∧ Keeps [.rax, .rcx, .rdx, .r13, .r14, .r15] s t := by
  apply WP.of_runBlock
  simp only [foldMul, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execMul, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    RegUpd.cf_setReg, ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have m1 := mulx_arith (s.gpr .rbp) orderLo
    have m2 := mulx_arith (s.gpr .rbp) orderHi
    have hc : (s.gpr .rbp).toNat * VG.Proof.Ed25519.X86_64.cL =
        (s.gpr .rbp).toNat * orderLo.toNat + 2 ^ 64 * ((s.gpr .rbp).toNat * orderHi.toNat) := by
      rw [← VG.Proof.Ed25519.X86_64.c_limbs, Nat.mul_add, Nat.mul_left_comm]
    have hb : (s.gpr .rbp).toNat * orderHi.toNat < 2 ^ 64 * 2 ^ 61 :=
      Nat.mul_lt_mul'' (s.gpr .rbp).isLt (by decide : orderHi.toNat < 2 ^ 61)
    have hz : (BitVec.ofNat 64 ((s.gpr .rbp).toNat * orderHi.toNat / 2 ^ 64)).toNat < 2 ^ 61 := by
      rw [BitVec.toNat_ofNat]; omega
    have ac := add_carry (BitVec.ofNat 64 ((s.gpr .rbp).toNat * orderLo.toNat / 2 ^ 64))
      (BitVec.ofNat 64 ((s.gpr .rbp).toNat * orderHi.toNat))
    have az := adc_carry (BitVec.ofNat 64 ((s.gpr .rbp).toNat * orderHi.toNat / 2 ^ 64)) 0
      (decide (2 ^ 64 ≤ (BitVec.ofNat 64 ((s.gpr .rbp).toNat * orderLo.toNat / 2 ^ 64)).toNat +
        (BitVec.ofNat 64 ((s.gpr .rbp).toNat * orderHi.toNat)).toNat))
    rw [hc]
    generalize (decide (2 ^ 64 ≤ (BitVec.ofNat 64 ((s.gpr .rbp).toNat * orderLo.toNat / 2 ^ 64)).toNat +
        (BitVec.ofNat 64 ((s.gpr .rbp).toNat * orderHi.toNat)).toNat)) = cy at ac az ⊢
    have hcy := Bool.toNat_le cy
    rw [show (0 : BitVec 64).toNat = 0 from rfl] at az
    rw [decide_eq_false (by omega), Bool.toNat_false] at az
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem mask_and (h : BitVec 64) (hh : h.toNat ≤ 1) (v : BitVec 64) :
    (v &&& BitVec.setWidth 64 (0 : BitVec 32) - h).toNat = h.toNat * v.toNat := by
  rcases (by omega : h.toNat = 0 ∨ h.toNat = 1) with e | e
  · rw [show h = 0#64 from BitVec.eq_of_toNat_eq (by rw [e]; rfl)]
    simp
  · rw [show h = 1#64 from BitVec.eq_of_toNat_eq (by rw [e]; rfl)]
    simp only [show BitVec.setWidth 64 (0 : BitVec 32) - 1#64 = BitVec.allOnes 64 by decide,
      BitVec.and_allOnes, BitVec.toNat_ofNat]
    omega

theorem foldMask_ok (s : State) (h1 : (s.gpr .r12).toNat ≤ 1) (h15 : (s.gpr .r15).toNat < 2 ^ 62) :
    WP isa (.block foldMask) s fun t => t.gpr .r13 = s.gpr .r13 ∧
      (t.gpr .r14).toNat + 2 ^ 64 * (t.gpr .r15).toNat =
        (s.gpr .r14).toNat + 2 ^ 64 * (s.gpr .r15).toNat + (s.gpr .r12).toNat * VG.Proof.Ed25519.X86_64.cL ∧
      Keeps [.rax, .rcx, .rdx, .r14, .r15] s t := by
  apply WP.of_runBlock
  simp only [foldMask, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, VG.X86_64.readSrc32, execAlu,
    State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have mx := VG.Proof.Ed25519.X86_64.mask_and (s.gpr .r12) h1 orderLo
    have my := VG.Proof.Ed25519.X86_64.mask_and (s.gpr .r12) h1 orderHi
    have hc : (s.gpr .r12).toNat * VG.Proof.Ed25519.X86_64.cL =
        (s.gpr .r12).toNat * orderLo.toNat + 2 ^ 64 * ((s.gpr .r12).toNat * orderHi.toNat) := by
      rw [← VG.Proof.Ed25519.X86_64.c_limbs, Nat.mul_add, Nat.mul_left_comm]
    have hH : orderHi.toNat < 2 ^ 61 := by decide
    have hy : (s.gpr .r12).toNat * orderHi.toNat < 2 ^ 61 := by
      rcases (by omega : (s.gpr .r12).toNat = 0 ∨ (s.gpr .r12).toNat = 1) with e | e <;> rw [e] <;> omega
    generalize orderLo &&& BitVec.setWidth 64 (0 : BitVec 32) - s.gpr .r12 = X at mx ⊢
    generalize orderHi &&& BitVec.setWidth 64 (0 : BitVec 32) - s.gpr .r12 = Y at my ⊢
    have ac := add_carry (s.gpr .r14) X
    generalize decide (2 ^ 64 ≤ (s.gpr .r14).toNat + X.toNat) = cy at ac ⊢
    have az := adc_carry (s.gpr .r15) Y cy
    have hcy := Bool.toNat_le cy
    rw [decide_eq_false (by omega), Bool.toNat_false] at az
    rw [hc]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

theorem eq_sub_of_chain {u T c : Nat} (hu : u < 2 ^ 256) (hT : T < L)
    (e : u + T = L + 2 ^ 256 * c) : u = L - T := by
  have := order_bound
  rcases Nat.lt_or_ge c 1 with h | h
  · obtain rfl : c = 0 := by omega
    omega
  · have : 2 ^ 256 ≤ 2 ^ 256 * c := Nat.le_mul_of_pos_right _ h
    omega

theorem foldSub_ok (s : State)
    (ht : (s.gpr .r13).toNat + 2 ^ 64 * (s.gpr .r14).toNat + 2 ^ 128 * (s.gpr .r15).toNat < L) :
    WP isa (.block foldSub) s fun t =>
      val4 (t.gpr .rax) (t.gpr .rcx) (t.gpr .rdx) (t.gpr .rbp) =
        L - ((s.gpr .r13).toNat + 2 ^ 64 * (s.gpr .r14).toNat + 2 ^ 128 * (s.gpr .r15).toNat) ∧
      Keeps [.rax, .rcx, .rdx, .rbp] s t := by
  apply WP.of_runBlock
  simp only [foldSub, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, VG.X86_64.readSrc32, execAlu,
    State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := chain_sub orderLo orderHi (BitVec.setWidth 64 (0 : BitVec 32)) orderTop (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) 0
    simp only at e
    have hL : val4 orderLo orderHi (BitVec.setWidth 64 (0 : BitVec 32)) orderTop = L := by decide
    rw [hL] at e
    have hT : val4 (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) 0 =
        (s.gpr .r13).toNat + 2 ^ 64 * (s.gpr .r14).toNat + 2 ^ 128 * (s.gpr .r15).toNat := by
      simp only [val4, show (0 : BitVec 64).toNat = 0 from rfl]; omega
    rw [hT] at e
    exact VG.Proof.Ed25519.X86_64.eq_sub_of_chain (VG.Proof.Ed25519.X86_64.val4_bound _ _ _ _) ht e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem eq_of_chain {u x c : Nat} (hx : x < 2 ^ 256) (e : u + 2 ^ 256 * c = x) : u = x := by
  rcases Nat.lt_or_ge c 1 with h | h
  · obtain rfl : c = 0 := by omega
    omega
  · have : 2 ^ 256 ≤ 2 ^ 256 * c := Nat.le_mul_of_pos_right _ h
    omega

theorem foldAdd_ok (s : State)
    (hs : VG.Proof.Ed25519.X86_64.scalarValue s + val4 (s.gpr .rax) (s.gpr .rcx) (s.gpr .rdx) (s.gpr .rbp) < 2 ^ 256) :
    WP isa (.block foldAdd) s fun t =>
      VG.Proof.Ed25519.X86_64.scalarValue t = VG.Proof.Ed25519.X86_64.scalarValue s + val4 (s.gpr .rax) (s.gpr .rcx) (s.gpr .rdx) (s.gpr .rbp) ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  apply WP.of_runBlock
  simp only [foldAdd, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := chain_add (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .rax) (s.gpr .rcx)
      (s.gpr .rdx) (s.gpr .rbp)
    simp only at e
    simp only [VG.Proof.Ed25519.X86_64.scalarValue, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    exact VG.Proof.Ed25519.X86_64.eq_of_chain hs e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- The registers `wordFold` changes. -/
def foldClob : List Reg := [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem wordFold_ok (s : State) (hr : VG.Proof.Ed25519.X86_64.scalarValue s < L) :
    WP isa (.block wordFold) s fun t => VG.Proof.Ed25519.X86_64.scalarValue t < 2 * L ∧
      VG.Proof.Ed25519.X86_64.scalarValue t % L = (VG.Proof.Ed25519.X86_64.scalarValue s * 2 ^ 64 + (s.gpr .rax).toNat) % L ∧ Keeps VG.Proof.Ed25519.X86_64.foldClob s t := by
  have hw := (s.gpr .rax).isLt
  obtain ⟨hlt, hlt2, hmod⟩ := VG.Proof.Ed25519.X86_64.fold_nat (VG.Proof.Ed25519.X86_64.scalarValue s) (s.gpr .rax).toNat hr hw
  have h0 := (s.gpr .r8).isLt; have h1 := (s.gpr .r9).isLt; have h2 := (s.gpr .r10).isLt
  have h3 : (s.gpr .r11).toNat < 2 ^ 61 := by
    have hL : L < 2 ^ 253 := by decide
    have := hr; simp only [VG.Proof.Ed25519.X86_64.scalarValue, val4] at this; omega
  -- `h` and `l` from the words
  have eh : (VG.Proof.Ed25519.X86_64.scalarValue s * 2 ^ 64 + (s.gpr .rax).toNat) / 2 ^ 252 =
      ((s.gpr .r10).toNat / 2 ^ 60 + 16 * ((s.gpr .r11).toNat % 2 ^ 60)) +
        2 ^ 64 * ((s.gpr .r11).toNat / 2 ^ 60) := by
    simp only [VG.Proof.Ed25519.X86_64.scalarValue, val4]; omega
  have el : (VG.Proof.Ed25519.X86_64.scalarValue s * 2 ^ 64 + (s.gpr .rax).toNat) % 2 ^ 252 =
      (s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .r8).toNat + 2 ^ 128 * (s.gpr .r9).toNat +
        2 ^ 192 * ((s.gpr .r10).toNat % 2 ^ 60) := by
    simp only [VG.Proof.Ed25519.X86_64.scalarValue, val4]; omega
  rw [eh] at hlt hlt2 hmod
  rw [el] at hlt2 hmod
  simp only [wordFold, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.foldPrep_ok s) fun a ⟨abp, a12, a8, a9, a10, a11, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.foldMul_ok a) fun b ⟨bt, kb⟩ => ?_
  have b12 : (b.gpr .r12).toNat ≤ 1 := by
    rw [kb.1 _ (by decide), a12]; omega
  have b15 : (b.gpr .r15).toNat < 2 ^ 62 := by
    have : (a.gpr .rbp).toNat * VG.Proof.Ed25519.X86_64.cL < 2 ^ 64 * VG.Proof.Ed25519.X86_64.cL :=
      Nat.mul_lt_mul_of_pos_right (a.gpr .rbp).isLt (by decide)
    simp only [VG.Proof.Ed25519.X86_64.cL] at this bt; omega
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.foldMask_ok b b12 b15) fun c ⟨c13, ct, kc⟩ => ?_
  have hT : (c.gpr .r13).toNat + 2 ^ 64 * (c.gpr .r14).toNat + 2 ^ 128 * (c.gpr .r15).toNat =
      ((s.gpr .r10).toNat / 2 ^ 60 + 16 * ((s.gpr .r11).toNat % 2 ^ 60) +
        2 ^ 64 * ((s.gpr .r11).toNat / 2 ^ 60)) * VG.Proof.Ed25519.X86_64.cL := by
    have e12 : b.gpr .r12 = a.gpr .r12 := kb.1 _ (by decide)
    rw [c13, Nat.add_mul, ← abp, ← a12, ← e12, Nat.mul_assoc]
    omega
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.foldSub_ok c (by rw [hT]; exact hlt)) fun d ⟨du, kd⟩ => ?_
  have hl : VG.Proof.Ed25519.X86_64.scalarValue d = (s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .r8).toNat + 2 ^ 128 * (s.gpr .r9).toNat +
      2 ^ 192 * ((s.gpr .r10).toNat % 2 ^ 60) := by
    simp only [VG.Proof.Ed25519.X86_64.scalarValue, val4]
    rw [kd.1 .r8 (by decide), kd.1 .r9 (by decide), kd.1 .r10 (by decide), kd.1 .r11 (by decide),
      kc.1 .r8 (by decide), kc.1 .r9 (by decide), kc.1 .r10 (by decide), kc.1 .r11 (by decide),
      kb.1 .r8 (by decide), kb.1 .r9 (by decide), kb.1 .r10 (by decide), kb.1 .r11 (by decide),
      a8, a9, a10, a11]
  rw [hT] at du
  refine WP.mono (VG.Proof.Ed25519.X86_64.foldAdd_ok d (by rw [hl, du]; have := order_bound; omega)) fun t ⟨tv, kt⟩ => ?_
  refine ⟨by rw [tv, hl, du]; exact hlt2, by rw [tv, hl, du]; exact hmod, ?_⟩
  exact (((ka.mono (by simp [VG.Proof.Ed25519.X86_64.foldClob])).trans (kb.mono (by simp [VG.Proof.Ed25519.X86_64.foldClob]))).trans
    ((kc.mono (by simp [VG.Proof.Ed25519.X86_64.foldClob])).trans (kd.mono (by simp [VG.Proof.Ed25519.X86_64.foldClob])))).trans (kt.mono (by simp [VG.Proof.Ed25519.X86_64.foldClob]))

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.ScalarLoop`. -/
section
/-!
# Scalar reduction: the eight-word loop

The invariant is the value modulo L of the already consumed top words of the
little-endian input. The body writes no memory.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Keeps)
open VG.Spec.Ed25519 (L bytesAt decodeLE)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

/-- The input from word `k` up: that word, and `2^64` times the words above it. -/
theorem words_step (m : Mem) (p : Addr) (k : Nat) (hk : k < 8) :
    decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * k)) (64 - 8 * k)) =
      (m.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat +
        2 ^ 64 * decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * (k + 1))) (64 - 8 * (k + 1))) := by
  have e : 64 - 8 * k = 8 + (64 - 8 * (k + 1)) := by omega
  have hs : bytesAt m (p + BitVec.ofNat 64 (8 * k)) (8 + (64 - 8 * (k + 1))) =
      bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8 ++
        bytesAt m (p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8) (64 - 8 * (k + 1)) :=
    Proof.X25519.bytesAt_add m _ 8 _
  have hw : decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8) =
      (m.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat := by
    rw [decodeLE_eq]; exact Proof.X25519.leNum_bytesAt_64 m _
  have ha : p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * k + 8 = 8 * (k + 1) by omega]
  rw [e, hs, decodeLE_append, VG.Proof.Ed25519.X86_64.bytesAt_length, hw, ha]

def wordRead : List Instr :=
  [.alu .sub .rbx (.imm 8), .mov .rax (.mem { base := .rsi, index := some .rbx })]

theorem wordRead_ok (s : State) (k : Nat) (hb : s.gpr .rbx = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block VG.Proof.Ed25519.X86_64.wordRead) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (8 * k) ∧
      t.gpr .rax = s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 64 ∧
      Keeps [.rbx, .rax] s t := by
  have hn : s.gpr .rbx - (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (8 * k) := by
    rw [hb, show (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 8 from rfl,
      show 8 * (k + 1) = 8 * k + 8 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [VG.Proof.Ed25519.X86_64.wordRead, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu,
    State.ea, State.load64, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, hn, ite_true, ite_false, reduceCtorEq,
    BitVec.mul_one, show BitVec.ofInt 64 (0 : Int) = BitVec.ofNat 64 0 from rfl,
    BitVec.add_zero, hr, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h.1, h.2, ite_false], rfl, rfl, rfl⟩

theorem scalar_test_zero : ∀ n < 64,
    (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == 0) = decide (n = 0) := by decide

theorem scalarTest_ok (s : State) (n : Nat) (hn : n < 64)
    (hb : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .test .rbx (.reg .rbx)]) s fun t =>
      t.zf = some (decide (n = 0)) ∧ VG.Proof.Ed25519.X86_64.scalarValue t = VG.Proof.Ed25519.X86_64.scalarValue s ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.zf_arithFlags, hb,
    VG.Proof.Ed25519.X86_64.scalar_test_zero n hn]
  exact ⟨trivial, rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The registers the loop changes. -/
def scalarBodyClob : List Reg := .rbx :: VG.Proof.Ed25519.X86_64.foldClob

theorem scalarWord_ok (s : State) (k : Nat) (hk : k < 8)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8)
    (hv : VG.Proof.Ed25519.X86_64.scalarValue s < L) :
    WP isa (.block scalarWord) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (8 * k) ∧ t.zf = some (decide (k = 0)) ∧
      VG.Proof.Ed25519.X86_64.scalarValue t = (VG.Proof.Ed25519.X86_64.scalarValue s * 2 ^ 64 +
        (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 64).toNat) % L ∧
      Keeps VG.Proof.Ed25519.X86_64.scalarBodyClob s t := by
  rw [show scalarWord = VG.Proof.Ed25519.X86_64.wordRead ++ (wordFold ++ (scalarSubtract ++ (scalarSelect ++
      ([.alu .test .rbx (.reg .rbx)] : List Instr)))) by
    simp only [scalarWord, VG.Proof.Ed25519.X86_64.wordRead, List.append_assoc, List.cons_append, List.nil_append],
    WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.wordRead_ok s k hb hr) fun a ⟨ab, ax, ka⟩ => ?_
  have av : VG.Proof.Ed25519.X86_64.scalarValue a = VG.Proof.Ed25519.X86_64.scalarValue s := by
    simp only [VG.Proof.Ed25519.X86_64.scalarValue, ka.1 .r8 (by decide), ka.1 .r9 (by decide),
      ka.1 .r10 (by decide), ka.1 .r11 (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.wordFold_ok a (av ▸ hv)) fun b ⟨b2, bm, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarSubtract_ok b) fun c ⟨cc, cu, csaved, kc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarSelect_ok c _ cc) fun d ⟨dv, kd⟩ => ?_
  have hb' : d.gpr .rbx = BitVec.ofNat 64 (8 * k) := by
    rw [kd.1 .rbx (by decide), kc.1 .rbx (by decide), kb.1 .rbx (by decide)]; exact ab
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarTest_ok d (8 * k) (by omega) hb') fun t ⟨tz, tv, kt⟩ => ?_
  have he := VG.Proof.Ed25519.X86_64.select_remainder (VG.Proof.Ed25519.X86_64.scalarValue b) (VG.Proof.Ed25519.X86_64.scalarValue c) b2 cu
  have k1 : Keeps VG.Proof.Ed25519.X86_64.scalarBodyClob s a := ka.mono (by simp [VG.Proof.Ed25519.X86_64.scalarBodyClob, VG.Proof.Ed25519.X86_64.foldClob])
  have k2 : Keeps VG.Proof.Ed25519.X86_64.scalarBodyClob a b := kb.mono (by simp [VG.Proof.Ed25519.X86_64.scalarBodyClob, VG.Proof.Ed25519.X86_64.foldClob])
  have k3 : Keeps VG.Proof.Ed25519.X86_64.scalarBodyClob b c := kc.mono (by simp [VG.Proof.Ed25519.X86_64.scalarBodyClob, VG.Proof.Ed25519.X86_64.foldClob])
  have k4 : Keeps VG.Proof.Ed25519.X86_64.scalarBodyClob c d := kd.mono (by simp [VG.Proof.Ed25519.X86_64.scalarBodyClob, VG.Proof.Ed25519.X86_64.foldClob])
  have k5 : Keeps VG.Proof.Ed25519.X86_64.scalarBodyClob d t := kt.mono (by simp)
  refine ⟨(kt.1 .rbx (by decide)).trans hb', by rw [tz]; simp; omega, ?_,
    k1.trans (k2.trans (k3.trans (k4.trans k5)))⟩
  simp only [decide_eq_true_eq] at dv
  rw [tv, dv, csaved, he, bm, av, ax]

theorem mod_step (a w : Nat) : (a % L * 2 ^ 64 + w) % L = (w + 2 ^ 64 * a) % L := by
  have hd := Nat.mod_add_div a L
  generalize a % L = r at hd ⊢
  generalize a / L = q at hd
  subst hd
  rw [← Nat.add_mul_mod_self_left (r * 2 ^ 64 + w) L (q * 2 ^ 64)]
  congr 1
  rw [Nat.mul_add, Nat.add_comm w, Nat.add_assoc, Nat.add_comm w, ← Nat.add_assoc, Nat.mul_comm (2 ^ 64) r,
    Nat.mul_left_comm (2 ^ 64) L q, Nat.mul_comm (2 ^ 64) q, ← Nat.mul_assoc]

structure ScalarInv (s₀ : State) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 8
  counter : s.gpr .rbx = BitVec.ofNat 64 (8 * n)
  value : VG.Proof.Ed25519.X86_64.scalarValue s =
    decodeLE (bytesAt s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 (8 * n)) (64 - 8 * n)) % L
  keeps : Keeps VG.Proof.Ed25519.X86_64.scalarBodyClob s₀ s

theorem scalarLoop_ok (s₀ : State) (hb : s₀.gpr .rbx = 64) (hz : VG.Proof.Ed25519.X86_64.scalarValue s₀ = 0)
    (hr : ∀ k < 8, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.loop (.block scalarWord) .ne) s₀ fun t =>
      VG.Proof.Ed25519.X86_64.scalarValue t = decodeLE (bytesAt s₀.mem (s₀.gpr .rsi) 64) % L ∧
      Keeps VG.Proof.Ed25519.X86_64.scalarBodyClob s₀ t := by
  apply WP.loop (VG.Proof.Ed25519.X86_64.ScalarInv s₀) (n := 8)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < 8 := by have := hi.bound; omega
    have hp : s.gpr .rsi = s₀.gpr .rsi := hi.keeps.1 .rsi (by decide)
    have hread : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8 := by
      rw [hi.keeps.2.2.1, hi.keeps.2.2.2, hp]; exact hr k hk
    have hv : VG.Proof.Ed25519.X86_64.scalarValue s < L := by rw [hi.value]; exact Nat.mod_lt _ order_pos
    refine WP.mono (VG.Proof.Ed25519.X86_64.scalarWord_ok s k hk hi.counter hread hv) fun t ⟨htb, htz, htv, htk⟩ => ?_
    have kt := hi.keeps.trans htk
    have vt : VG.Proof.Ed25519.X86_64.scalarValue t =
        decodeLE (bytesAt s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 (8 * k)) (64 - 8 * k)) % L := by
      rw [htv, hi.value, hp, hi.keeps.2.1, VG.Proof.Ed25519.X86_64.words_step _ _ k hk, Nat.succ_eq_add_one, VG.Proof.Ed25519.X86_64.mod_step]
    by_cases hk0 : k = 0
    · subst hk0
      refine Or.inl ⟨by simp only [eval, htz, decide_true, Option.map_some, Bool.not_true], ?_, kt⟩
      simpa only [Nat.mul_zero, BitVec.add_zero, Nat.sub_zero] using vt
    · exact Or.inr ⟨by simp only [eval, htz, decide_eq_false hk0, Option.map_some, Bool.not_false],
        k, by omega, ⟨by omega, by omega, htb, vt, kt⟩⟩
  · refine ⟨by decide, by decide, hb, ?_, fun _ _ => rfl, rfl, rfl, rfl⟩
    rw [hz]
    rfl

end VG.Proof.Ed25519.X86_64
end

/-!
# Scalar reduction: memory and callee-saved registers

Saving and restoring use the first 48 bytes of the scratch argument, and the
next 8 hold the output's address while the loop keeps the scratch in `rdi`.
The arithmetic loop changes no memory.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (at_ saved zero4)
open VG.Proof.X25519.X86_64

theorem scalarSave_ok {s : State} {base : Addr} (hc : s.gpr .rdx = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarSave) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Outside base 0 48 s.mem s'.mem ∧
      Saved base s.gpr s'.mem := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base base hd (by omega)⟩
  apply WP.of_runBlock
  simp only [scalarSave, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
    exec, ea_at, hc, State.store64, w 0 (by omega), w 8 (by omega), w 16 (by omega),
    w 24 (by omega), w 32 (by omega), w 40 (by omega), ite_true, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_, fun rd hrd => ?_⟩
  · exact ((((((Outside.refl base 0 48 s.mem).writeW (by omega) (by omega) (by omega) _).writeW
      (by omega) (by omega) (by omega) _).writeW (by omega) (by omega) (by omega) _).writeW
      (by omega) (by omega) (by omega) _).writeW (by omega) (by omega) (by omega) _).writeW
      (by omega) (by omega) (by omega) _
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [word_writeW_sep, word_writeW_self]

theorem scalarRestore_ok {s : State} {base : Addr} (hb : s.gpr .rdx = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {g : Reg → BitVec 64}
    (hsv : Saved base g s.mem) :
    WP isa (.block scalarRestore) s fun s' =>
      (∀ rd ∈ saved, s'.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hr : ∀ d, d + 8 ≤ 8192 → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, Offset.contains_base base hd (by omega)⟩
  have v : ∀ rd ∈ saved, s.mem.readW (off base rd.2) 64 = g rd.1 := hsv
  apply WP.of_runBlock
  simp only [scalarRestore, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some,
    runBlock_nil, exec, VG.X86_64.readSrc, State.load64, ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, hb, hr 0 (by omega), hr 8 (by omega),
    hr 16 (by omega), hr 24 (by omega), hr 32 (by omega), hr 40 (by omega), ite_true, ite_false,
    reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun rd hrd => ?_, fun r hr => ?_, trivial, trivial, trivial⟩
  · have e := v rd hrd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa only [RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq] using e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem scalarOut_ok {s : State} {q : Addr} (hq : s.gpr .rdi = q) (hw : (⟨q, 32⟩ : Region) ∈ s.wr) :
    WP isa (.block ([.store (at_ .rdi 0) .r8, .store (at_ .rdi 8) .r9, .store (at_ .rdi 16) .r10,
      .store (at_ .rdi 24) .r11] : List Instr)) s fun s' =>
      s'.mem = st4 s.mem q 0 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 32 → InRegions s.wr (off q d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base q hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hq, State.store64,
    w 0 (by omega), w 8 (by omega), w 16 (by omega), w 24 (by omega), ite_true, Option.some.injEq,
    exists_eq_left']
  exact ⟨rfl, trivial, trivial, trivial⟩

theorem scalarInit_ok (s : State) :
    WP isa (.block (zero4 ++ ([.mov32 .rbx (.imm 64)] : List Instr))) s fun t =>
      t.gpr .rbx = 64 ∧ VG.Proof.Ed25519.X86_64.scalarValue t = 0 ∧ Keeps [.r8, .r9, .r10, .r11, .rbx] s t := by
  apply WP.of_runBlock
  simp only [zero4, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, State.setReg32,
    Option.map_some, Option.some.injEq, exists_eq_left', VG.Proof.Ed25519.X86_64.scalarValue, RegUpd.gpr_setReg,
    ite_true, ite_false, reduceCtorEq]
  refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- The output's address to byte 48 of the scratch (in `rdx`), and the scratch into `rdi`. -/
theorem stashOut_ok {s : State} {base : Addr} (hb : s.gpr .rdx = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block [.store (at_ .rdx 48) .rdi, .mov .rdi (.reg .rdx)]) s fun t =>
      t.mem = s.mem.writeW (off base 48) (s.gpr .rdi) ∧ t.gpr .rdi = base ∧
      (∀ r, r ≠ .rdi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : InRegions s.wr (off base 48) 8 := ⟨_, hw, Offset.contains_base base (by omega) (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, ea_at, hb, State.store64, w,
    ite_true, RegUpd.gpr_setReg, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial, fun r hr => by simp only [hr, ite_false], rfl, rfl⟩

/-- The scratch from `rdi` back into `rdx`, and the output's address from byte 48 into `rdi`. -/
theorem finishArgs_ok {s : State} {base : Addr} (hb : s.gpr .rdi = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarFinishArgs) s fun t =>
      t.gpr .rdx = base ∧ t.gpr .rdi = s.mem.readW (off base 48) 64 ∧
      (∀ r, r ≠ .rdx → r ≠ .rdi → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : InRegions (s.rd ++ s.wr) (off base 48) 8 :=
    ⟨_, List.mem_append_right _ hw, Offset.contains_base base (by omega) (by omega)⟩
  apply WP.of_runBlock
  simp only [scalarFinishArgs, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, ea_at,
    State.load64, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, hb, w,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h1 h2 => by simp only [h1, h2, ite_false], trivial, trivial, trivial⟩

theorem scratchFrame {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') (hn : o + n ≤ 8192) : Frame [⟨base, 8192⟩] m m' := by
  intro x hx
  apply h x
  right
  have hn' := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hn'
  simp only [ofs]
  omega

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.MulAddMemory`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.WideMul`. -/
section
/-! The eight product words represent the full unsigned product. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64
open VG.Proof.X25519.X86_64

def wideValue (s : State) : Nat :=
  val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
    2 ^ 256 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15)

theorem wideAccumulate_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat}
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (wideAccumulate a b)) s fun t =>
      VG.Proof.Ed25519.X86_64.wideValue t = val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
        fe s.mem base a * fe s.mem base b ∧ Keeps clob s t := by
  have g : ∀ {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg), r ∉ rs → y.gpr r = x.gpr r :=
    fun k r h => k.1 r h
  rw [show wideAccumulate a b = row a b 0 ++ (row a b 1 ++ (row a b 2 ++ row a b 3)) by
    simp only [wideAccumulate, List.append_assoc]]
  rw [WP.block_append_iff, row0]
  refine WP.mono (rowR_ok hs (by omega) hb (by decide)) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff, row1]
  refine WP.mono (rowR_ok hs₁ (by omega) hb (by decide)) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff, row2]
  refine WP.mono (rowR_ok hs₂ (by omega) hb (by decide)) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  rw [row3]
  refine WP.mono (rowR_ok hs₃ (by omega) hb (by decide)) fun s₄ ⟨e4, k4⟩ => ?_
  refine ⟨?_, ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide)) |>.trans (k4.mono (by decide))⟩
  change val4 (s₄.gpr .r8) (s₄.gpr .r9) (s₄.gpr .r10) (s₄.gpr .r11) +
    2 ^ 256 * val4 (s₄.gpr .r12) (s₄.gpr .r13) (s₄.gpr .r14) (s₄.gpr .r15) = _
  rw [fe_mul_expand]
  -- Every row read the same memory.
  rw [k1.2.1] at e2
  rw [k2.2.1, k1.2.1] at e3
  rw [k3.2.1, k2.2.1, k1.2.1] at e4
  -- The registers along the way.
  have r1 := g k2 .r8 (by decide); have r2 := g k3 .r8 (by decide); have r3 := g k4 .r8 (by decide)
  have q2 := g k3 .r9 (by decide); have q3 := g k4 .r9 (by decide); have q4 := g k4 .r10 (by decide)
  simp only [val4] at e1 e2 e3 e4 ⊢
  rw [r3, r2, r1, q3, q2, q4]
  omega_using [e1, e2, e3, e4]

/-- Reuse the checked four-KiB arithmetic within Ed25519's larger scratch
argument. Execution is lifted by the framework's memory-permission theorem. -/
theorem wideAccumulate8192_ok {s : State} {base : Addr}
    (hp : s.gpr .rdi = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) {a b : Nat} (ha : Slot a) (hb : Slot b) :
    WP isa (.block (wideAccumulate a b)) s fun t =>
      VG.Proof.Ed25519.X86_64.wideValue t = val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
        fe s.mem base a * fe s.mem base b ∧ Keeps clob s t := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hs : Scr narrow base := ⟨hp, List.mem_singleton_self _, by omega⟩
  obtain ⟨tr, t, he, hv, hk⟩ := VG.Proof.Ed25519.X86_64.wideAccumulate_ok hs ha hb
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hw, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, hv, hk.1, hk.2.1, rfl, rfl⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

end VG.Proof.Ed25519.X86_64
end

/-! Moving the scalar operands and full product through scratch. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64
open VG.Proof.X25519.X86_64

theorem loadWords_ok (s : State) (src : Reg) (hsrc : src ∉ [Reg.r8, .r9, .r10, .r11])
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (s.gpr src) d) 8) :
    WP isa (.block (loadWords src)) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = fe s.mem (s.gpr src) 0 ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hsrc
  apply WP.of_runBlock
  simp only [loadWords, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, hsrc.1, hsrc.2.1, hsrc.2.2.1,
    hr 0 (by decide), hr 8 (by decide), hr 16 (by decide), hr 24 (by decide),
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r h => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [RegUpd.gpr_setReg, h.1, h.2.1, h.2.2.1, h.2.2.2, ite_false]

theorem stores8192_ok {s : State} {base : Addr} (hp : s.gpr .rdi = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {o : Nat} (ho : o + 32 ≤ 8192)
    (a b c d : Reg) :
    WP isa (.block (stores o a b c d)) s fun t =>
      t.mem = st4 s.mem base o (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [stores, runBlock_cons, runStep_some, runBlock_nil, exec, ea_sc, hp, State.store64,
    w o (by omega), w (o + 8) (by omega), w (o + 16) (by omega), w (o + 24) (by omega),
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial, trivial, trivial⟩

theorem copyScalar_ok {s : State} {base : Addr} (hp : s.gpr .rdi = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (src : Reg) (hsrc : src ∉ [Reg.r8, .r9, .r10, .r11])
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (s.gpr src) d) 8)
    (o : Nat) (ho : o + 32 ≤ 8192) :
    WP isa (.block (copyScalar src o)) s fun t =>
      fe t.mem base o = fe s.mem (s.gpr src) 0 ∧
      (∀ r, r ∉ [Reg.r8, .r9, .r10, .r11] → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Outside base o 32 s.mem t.mem := by
  rw [copyScalar, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.loadWords_ok s src hsrc hr) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86_64.stores8192_ok ((hk.1 .rdi (by decide)).trans hp) (hk.2.2.2 ▸ hw)
    ho .r8 .r9 .r10 .r11) fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  refine ⟨?_, fun r h => (congrFun hg r).trans (hk.1 r h), hrd.trans hk.2.2.1,
    hwr.trans hk.2.2.2, ?_⟩
  · rw [hm, fe_st4 _ _ (by omega)]; exact hv
  · rw [hm, hk.2.1]; exact st4_outside _ _ (by omega) _ _ _ _

theorem mulAddSave_ok {s : State} {base : Addr} (hc : s.gpr .r8 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block mulAddSave) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Outside base 0 48 s.mem s'.mem ∧
      Saved base s.gpr s'.mem := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base base hd (by omega)⟩
  apply WP.of_runBlock
  simp only [mulAddSave, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
    exec, ea_at, hc, State.store64, w 0 (by omega), w 8 (by omega), w 16 (by omega),
    w 24 (by omega), w 32 (by omega), w 40 (by omega), ite_true, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_, fun rd hrd => ?_⟩
  · exact ((((((Outside.refl base 0 48 s.mem).writeW (by omega) (by omega) (by omega) _).writeW
      (by omega) (by omega) (by omega) _).writeW (by omega) (by omega) (by omega) _).writeW
      (by omega) (by omega) (by omega) _).writeW (by omega) (by omega) (by omega) _).writeW
      (by omega) (by omega) (by omega) _
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [word_writeW_sep, word_writeW_self]


end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.MulAddCodec`. -/
section

/-! Full-width scalars and byte encodings in the working space. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64
open VG.Proof.X25519.X86_64
open VG.Spec.Ed25519 (bytesAt decodeLE)

theorem decodeLE_words (m : Mem) (base : Addr) (o : Nat) :
    decodeLE (bytesAt m (off base o) 32) = fe m base o := by
  rw [decodeLE_eq]
  change Proof.X25519.leNum (Spec.X25519.bytesAt m (off base o) 32) = _
  rw [Proof.X25519.leNum_bytesAt_words64]
  simp only [fe, val4, Proof.X25519.X86_64.word, off]
  rw [show base + BitVec.ofNat 64 o + 8 = base + BitVec.ofNat 64 (o + 8) from Offset.add_add ..,
    show base + BitVec.ofNat 64 o + 16 = base + BitVec.ofNat 64 (o + 16) from Offset.add_add ..,
    show base + BitVec.ofNat 64 o + 24 = base + BitVec.ofNat 64 (o + 24) from Offset.add_add ..]

theorem decodeLE_wide (m : Mem) (base : Addr) :
    decodeLE (bytesAt m (off base 128) 64) = fe m base 128 + 2 ^ 256 * fe m base 160 := by
  have hb : bytesAt m (off base 128) 64 =
      bytesAt m (off base 128) 32 ++ bytesAt m (off base 160) 32 := by
    have h := Proof.X25519.bytesAt_add m (off base 128) 32 32
    rw [Offset.add_add] at h
    exact h
  rw [hb, decodeLE_append, VG.Proof.Ed25519.X86_64.bytesAt_length, VG.Proof.Ed25519.X86_64.decodeLE_words, VG.Proof.Ed25519.X86_64.decodeLE_words]

theorem fe_frame {base p : Addr} {m m' : Mem} (hf : Frame [⟨base, 8192⟩] m m')
    (hp : (⟨p, 32⟩ : Region).Disjoint ⟨base, 8192⟩) : fe m' p 0 = fe m p 0 := by
  have h : ∀ d, d + 8 ≤ 32 → m'.readW (off p d) 64 = m.readW (off p d) 64 := fun d hd =>
    hf.readW (r := ⟨p, 32⟩) (Offset.contains_base _ hd (by omega))
      (by simpa only [List.mem_singleton, forall_eq]) (by decide)
  simp only [fe, val4, Proof.X25519.X86_64.word, h 0 (by decide), h 8 (by decide), h 16 (by decide), h 24 (by decide)]

theorem storeWide_ok {s : State} {base : Addr} (hp : s.gpr .rdi = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block storeWide) s fun t =>
      decodeLE (bytesAt t.mem (off base 128) 64) = VG.Proof.Ed25519.X86_64.wideValue s ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Outside base 128 64 s.mem t.mem := by
  rw [storeWide, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.stores8192_ok hp hw (by decide) .r8 .r9 .r10 .r11) fun t ⟨hm, hg, hrd, hwr⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86_64.stores8192_ok ((congrFun hg _).trans hp) (hwr ▸ hw) (by decide)
    .r12 .r13 .r14 .r15) fun u ⟨hm', hg', hrd', hwr'⟩ => ?_
  have ot : Outside base 128 32 s.mem t.mem := by rw [hm]; exact st4_outside _ _ (by decide) _ _ _ _
  have ou : Outside base 160 32 t.mem u.mem := by rw [hm']; exact st4_outside _ _ (by decide) _ _ _ _
  refine ⟨?_, hg'.trans hg, hrd'.trans hrd, hwr'.trans hwr,
    (ot.mono (by decide) (by decide)).trans (ou.mono (by decide) (by decide))⟩
  rw [VG.Proof.Ed25519.X86_64.decodeLE_wide, ou.fe (by decide) (by decide), hm', fe_st4 _ _ (by decide),
    hm, fe_st4 _ _ (by decide), hg]
  rfl

/-- The wide value's address into `rsi`, and the output's address (`rbx`) to byte 48 of the
scratch (`rdi`). -/
theorem reduceArgs_ok {s : State} {base : Addr} (hb : s.gpr .rdi = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block reduceArgs) s fun t =>
      t.gpr .rsi = off base 128 ∧ t.mem = s.mem.writeW (off base 48) (s.gpr .rbx) ∧
      (∀ r, r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : InRegions s.wr (off base 48) 8 := ⟨_, hw, Offset.contains_base base (by omega) (by omega)⟩
  apply WP.of_runBlock
  simp only [reduceArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, ea_at,
    State.store64, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, hb, w, ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  exact ⟨rfl, trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial⟩

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMain`. -/
section

/-!
# Scalar reduction: the complete function

The small target-specific contract below is implied by the merged signature
contract. It records the separation needed to preserve the input and return
address while saving registers, and the output's address while the loop keeps
it in the scratch.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (at_ saved zero4)
open VG.Proof.X25519.X86_64
open VG.Spec.Ed25519 (bytesAt)

def scalarReduceLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rsi, 64⟩] ∧ s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩] ∧
    (⟨s.gpr .rsi, 64⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 32⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (⟨s.gpr .rdi, 32⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩
  post s t := bytesAt t.mem (s.gpr .rdi) 32 =
    Spec.Ed25519.scalarReduce (bytesAt s.mem (s.gpr .rsi) 64)
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧
    s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx

theorem scalarSave_frame {base : Addr} {m m' : Mem} (h : Outside base 0 48 m m') :
    Frame [⟨base, 8192⟩] m m' := by
  intro x hx
  apply h x
  right
  have hn := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hn
  simp only [ofs]
  omega

theorem bytesAt_frame {m m' : Mem} {p base : Addr} (hf : Frame [⟨base, 8192⟩] m m')
    (hd : (⟨p, 64⟩ : Region).Disjoint ⟨base, 8192⟩) : bytesAt m' p 64 = bytesAt m p 64 := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, 64⟩) (by simpa only [List.mem_singleton, forall_eq])
    (by change 64 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

theorem encodeLE_eq (n x : Nat) : Spec.Ed25519.encodeLE n x = Proof.X25519.leBytes n x := by
  simp only [Spec.Ed25519.encodeLE, Proof.X25519.leBytes, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem scalarReduce_correct {s : State} (hs : scalarReduceLocal.pre s) :
    WP isa scalarReduce s fun t => gprPreserved s t ∧ scalarReduceLocal.post s t := by
  obtain ⟨hr, hw, hd, hro, hrs, -⟩ := hs
  have hws : (⟨s.gpr .rdx, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [scalarReduce]
  apply WP.seq
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarSave_ok rfl hws) fun s₁ ⟨g₁, rd₁, wr₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.stashOut_ok (base := s.gpr .rdx) (by rw [g₁]) (by rw [wr₁]; exact hws))
    fun s₁' ⟨m₁', di₁', g₁', rd₁', wr₁'⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarInit_ok s₁') fun s₂ ⟨b₂, v₂, k₂⟩ => ?_
  have rsi₂ : s₂.gpr .rsi = s.gpr .rsi :=
    (k₂.1 _ (by decide)).trans ((g₁' _ (by decide)).trans (congrFun g₁ _))
  have rdi₂ : s₂.gpr .rdi = s.gpr .rdx := (k₂.1 _ (by decide)).trans di₁'
  have mem₂ : s₂.mem = s₁.mem.writeW (off (s.gpr .rdx) 48) (s.gpr .rdi) := by
    rw [k₂.2.1, m₁', g₁]
  have rw₂ : s₂.rd = s.rd ∧ s₂.wr = s.wr := ⟨by rw [k₂.2.2.1, rd₁', rd₁], by rw [k₂.2.2.2, wr₁', wr₁]⟩
  have read₂ : ∀ k < 8, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8 := by
    intro k hk
    refine ⟨⟨s.gpr .rsi, 64⟩, ?_, ?_⟩
    · rw [rw₂.1, hr]; simp
    · rw [rsi₂]; exact Offset.contains_base _ (by omega) (by omega)
  have o₂ : Outside (s.gpr .rdx) 48 8 s₁.mem s₂.mem := by
    rw [mem₂]; exact writeW_outside _ _ _ (by omega)
  have fm₂ : Frame [⟨s.gpr .rdx, 8192⟩] s.mem s₂.mem :=
    (VG.Proof.Ed25519.X86_64.scalarSave_frame o₁).trans (VG.Proof.Ed25519.X86_64.scratchFrame o₂ (by decide))
  apply WP.seq
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarLoop_ok s₂ b₂ v₂ read₂) fun s₃ ⟨v₃, k₃⟩ => ?_
  have rdi₃ : s₃.gpr .rdi = s.gpr .rdx := (k₃.1 _ (by decide)).trans rdi₂
  have wr₃ : s₃.wr = s.wr := k₃.2.2.2.trans rw₂.2
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.finishArgs_ok rdi₃ (wr₃ ▸ hws)) fun s₄ ⟨dx₄, di₄, g₄', m₄', rd₄', wr₄'⟩ => ?_
  have sv₄ : Saved (s.gpr .rdx) s.gpr s₄.mem := by
    rw [m₄', k₃.2.1]; exact sv₁.outside o₂ (by decide)
  have out₄ : s₄.gpr .rdi = s.gpr .rdi := by
    rw [di₄, k₃.2.1, mem₂]; exact Mem.readW_writeW_self64 _ _ _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarRestore_ok dx₄ (by rw [wr₄', wr₃]; exact hws) sv₄)
    fun s₅ ⟨r₅, g₅, m₅, _, wr₅⟩ => ?_
  have rdi₅ : s₅.gpr .rdi = s.gpr .rdi := (g₅ _ (by decide)).trans out₄
  have hwo : (⟨s.gpr .rdi, 32⟩ : Region) ∈ s₅.wr := by rw [wr₅, wr₄', wr₃, hw]; simp
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarOut_ok rdi₅ hwo) fun t ⟨mt, gt, _, _⟩ => ?_
  have fm : Frame [⟨s.gpr .rdx, 8192⟩] s.mem s₅.mem := by
    rw [m₅, m₄', k₃.2.1]; exact fm₂
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [gt]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r₅ (.rbx, 0) (by decide)
    · exact r₅ (.rbp, 8) (by decide)
    · rw [g₅ _ (by decide), g₄' _ (by decide) (by decide), k₃.1 _ (by decide), k₂.1 _ (by decide),
        g₁' _ (by decide), g₁]
    · exact r₅ (.r12, 16) (by decide)
    · exact r₅ (.r13, 24) (by decide)
    · exact r₅ (.r14, 32) (by decide)
    · exact r₅ (.r15, 40) (by decide)
  · have ft : Frame [⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rdi, 32⟩] s.mem t.mem := by
      rw [mt]
      have c : ∀ d, d + 8 ≤ 32 → (⟨s.gpr .rdi, 32⟩ : Region).Contains (off (s.gpr .rdi) d) (64 / 8) :=
        fun d hd => Offset.contains_base _ hd (by omega)
      have hm : (⟨s.gpr .rdi, 32⟩ : Region) ∈ [⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rdi, 32⟩] := by simp
      exact ((((fm.mono (by simp)).writeW hm _ (c 0 (by decide))).writeW hm _
        (c 8 (by decide))).writeW hm _ (c 16 (by decide))).writeW hm _ (c 24 (by decide))
    exact ft.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hrs
      · exact hro) (by decide)
  · change bytesAt t.mem (s.gpr .rdi) 32 = Spec.Ed25519.scalarReduce _
    rw [mt]
    change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    rw [bytesAt_st4, Spec.Ed25519.scalarReduce, VG.Proof.Ed25519.X86_64.encodeLE_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    change VG.Proof.Ed25519.X86_64.scalarValue s₅ = _
    have val₅ : VG.Proof.Ed25519.X86_64.scalarValue s₅ = VG.Proof.Ed25519.X86_64.scalarValue s₃ := by
      simp only [VG.Proof.Ed25519.X86_64.scalarValue, g₅ .r8 (by decide), g₅ .r9 (by decide),
        g₅ .r10 (by decide), g₅ .r11 (by decide), g₄' .r8 (by decide) (by decide),
        g₄' .r9 (by decide) (by decide), g₄' .r10 (by decide) (by decide), g₄' .r11 (by decide) (by decide)]
    rw [val₅, v₃, rsi₂, VG.Proof.Ed25519.X86_64.bytesAt_frame fm₂ hd]

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.MulAddVerified`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.MulAddMain`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.MulAddSetup`. -/
section
/-! Save the caller's registers and prepare the scalar operands. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64
open VG.Proof.X25519.X86_64

structure MulAddPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rsi, 32⟩, ⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, 32⟩]
  wr : s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .r8, 8192⟩]
  r_sc : (⟨s.gpr .rsi, 32⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩
  k_sc : (⟨s.gpr .rdx, 32⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩
  s_sc : (⟨s.gpr .rcx, 32⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩
  ret_out : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 32⟩
  ret_sc : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩
  nowrap : (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64

structure MulAddReady (s₀ s : State) : Prop where
  base : s.gpr .rdi = s₀.gpr .r8
  out : s.gpr .rbx = s₀.gpr .rdi
  rsp : s.gpr .rsp = s₀.gpr .rsp
  value : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) = fe s₀.mem (s₀.gpr .rsi) 0
  left : fe s.mem (s₀.gpr .r8) 64 = fe s₀.mem (s₀.gpr .rdx) 0
  right : fe s.mem (s₀.gpr .r8) 96 = fe s₀.mem (s₀.gpr .rcx) 0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved (s₀.gpr .r8) s₀.gpr s.mem
  frame : Frame [⟨s₀.gpr .r8, 8192⟩] s₀.mem s.mem

theorem mulAddArgs_ok (s : State) :
    WP isa (.block [.mov .rbx (.reg .rdi), .mov .rdi (.reg .r8)]) s fun t =>
      t.gpr .rbx = s.gpr .rdi ∧ t.gpr .rdi = s.gpr .r8 ∧ Keeps [.rbx, .rdi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem mulAddSetup_ok {s : State} (hs : VG.Proof.Ed25519.X86_64.MulAddPre s) :
    WP isa (.block mulAddSetup) s (VG.Proof.Ed25519.X86_64.MulAddReady s) := by
  have hw : (⟨s.gpr .r8, 8192⟩ : Region) ∈ s.wr := by rw [hs.wr]; simp
  rw [show mulAddSetup = mulAddSave ++ (([.mov .rbx (.reg .rdi), .mov .rdi (.reg .r8)] :
    List Instr) ++ (copyScalar .rdx 64 ++ (copyScalar .rcx 96 ++ loadScalar))) by
    simp only [mulAddSetup, List.append_assoc], WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.mulAddSave_ok rfl hw) fun s₁ ⟨g₁, rd₁, wr₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.mulAddArgs_ok s₁) fun s₂ ⟨out₂, base₂, k₂⟩ => ?_
  have hp₂ : s₂.gpr .rdi = s.gpr .r8 := base₂.trans (congrFun g₁ _)
  have hw₂ : (⟨s.gpr .r8, 8192⟩ : Region) ∈ s₂.wr := by rw [k₂.2.2.2, wr₁]; exact hw
  have g₂ : ∀ r, r ∉ [Reg.rbx, .rdi] → s₂.gpr r = s.gpr r :=
    fun r h => (k₂.1 r h).trans (congrFun g₁ r)
  have fm₂ : Frame [⟨s.gpr .r8, 8192⟩] s.mem s₂.mem := by
    rw [k₂.2.1]; exact VG.Proof.Ed25519.X86_64.scratchFrame o₁ (by decide)
  have hr₂ : ∀ d, d + 8 ≤ 32 → InRegions (s₂.rd ++ s₂.wr) (off (s₂.gpr .rdx) d) 8 := by
    intro d hd
    refine ⟨⟨s.gpr .rdx, 32⟩, ?_, ?_⟩
    · rw [k₂.2.2.1, rd₁, hs.rd]; simp
    · rw [g₂ .rdx (by decide)]; exact Offset.contains_base _ hd (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.copyScalar_ok hp₂ hw₂ .rdx (by decide) hr₂ 64 (by decide))
    fun s₃ ⟨v₃, g₃, rd₃, wr₃, o₃⟩ => ?_
  have hp₃ : s₃.gpr .rdi = s.gpr .r8 := (g₃ _ (by decide)).trans hp₂
  have hw₃ : (⟨s.gpr .r8, 8192⟩ : Region) ∈ s₃.wr := wr₃ ▸ hw₂
  have fm₃ := fm₂.trans (VG.Proof.Ed25519.X86_64.scratchFrame o₃ (by decide))
  have rcx₃ : s₃.gpr .rcx = s.gpr .rcx := (g₃ _ (by decide)).trans (g₂ _ (by decide))
  have hr₃ : ∀ d, d + 8 ≤ 32 → InRegions (s₃.rd ++ s₃.wr) (off (s₃.gpr .rcx) d) 8 := by
    intro d hd
    refine ⟨⟨s.gpr .rcx, 32⟩, ?_, ?_⟩
    · rw [rd₃, k₂.2.2.1, rd₁, hs.rd]; simp
    · rw [rcx₃]; exact Offset.contains_base _ hd (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.copyScalar_ok hp₃ hw₃ .rcx (by decide) hr₃ 96 (by decide))
    fun s₄ ⟨v₄, g₄, rd₄, wr₄, o₄⟩ => ?_
  have fm₄ := fm₃.trans (VG.Proof.Ed25519.X86_64.scratchFrame o₄ (by decide))
  have rsi₄ : s₄.gpr .rsi = s.gpr .rsi :=
    (g₄ _ (by decide)).trans ((g₃ _ (by decide)).trans (g₂ _ (by decide)))
  have hr₄ : ∀ d, d + 8 ≤ 32 → InRegions (s₄.rd ++ s₄.wr) (off (s₄.gpr .rsi) d) 8 := by
    intro d hd
    refine ⟨⟨s.gpr .rsi, 32⟩, ?_, ?_⟩
    · rw [rd₄, rd₃, k₂.2.2.1, rd₁, hs.rd]; simp
    · rw [rsi₄]; exact Offset.contains_base _ hd (by omega)
  refine WP.mono (VG.Proof.Ed25519.X86_64.loadWords_ok s₄ .rsi (by decide) hr₄) fun t ⟨vt, kt⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kt.1 _ (by decide), g₄ _ (by decide)]; exact hp₃
  · rw [kt.1 _ (by decide), g₄ _ (by decide), g₃ _ (by decide), out₂, g₁]
  · rw [kt.1 _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide)]
  · rw [vt, rsi₄, VG.Proof.Ed25519.X86_64.fe_frame fm₄ hs.r_sc]
  · rw [kt.2.1, o₄.fe (by decide) (by decide), v₃, g₂ _ (by decide), VG.Proof.Ed25519.X86_64.fe_frame fm₂ hs.k_sc]
  · rw [kt.2.1, v₄, rcx₃, VG.Proof.Ed25519.X86_64.fe_frame fm₃ hs.s_sc]
  · rw [kt.2.2.1, rd₄, rd₃, k₂.2.2.1, rd₁]
  · rw [kt.2.2.2, wr₄, wr₃, k₂.2.2.2, wr₁]
  · have sv₂ : Saved (s.gpr .r8) s.gpr s₂.mem := by rw [k₂.2.1]; exact sv₁
    rw [kt.2.1]; exact (sv₂.outside o₃ (by decide)).outside o₄ (by decide)
  · rw [kt.2.1]; exact fm₄

end VG.Proof.Ed25519.X86_64
end

/-! Full-width multiply-add followed by subgroup reduction. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64
open VG.Proof.X25519.X86_64
open VG.Spec.Ed25519 (bytesAt decodeLE)

def scalarMulAddLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rsi, 32⟩, ⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, 32⟩] ∧
    s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .r8, 8192⟩] ∧
    (⟨s.gpr .rsi, 32⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (⟨s.gpr .rdx, 32⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (⟨s.gpr .rcx, 32⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 32⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rdi, 32⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩
  post s t := bytesAt t.mem (s.gpr .rdi) 32 = Spec.Ed25519.scalarMulAdd
    (bytesAt s.mem (s.gpr .rsi) 32) (bytesAt s.mem (s.gpr .rdx) 32) (bytesAt s.mem (s.gpr .rcx) 32)
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧
    s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx ∧
    s.gpr .rcx = t.gpr .rcx ∧ s.gpr .r8 = t.gpr .r8

theorem MulAddPre.of {s : State} (h : scalarMulAddLocal.pre s) : VG.Proof.Ed25519.X86_64.MulAddPre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

theorem scalarMulAdd_correct {s : State} (hs : VG.Proof.Ed25519.X86_64.MulAddPre s) :
    WP isa scalarMulAdd s fun t => gprPreserved s t ∧ scalarMulAddLocal.post s t := by
  have hw : (⟨s.gpr .r8, 8192⟩ : Region) ∈ s.wr := by rw [hs.wr]; simp
  rw [scalarMulAdd]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.mulAddSetup_ok hs) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.wideAccumulate8192_ok h₁.base (h₁.wr ▸ hw) hs.nowrap
    (by decide) (by decide)) fun s₂ ⟨v₂, k₂⟩ => ?_)
  have prod₂ : VG.Proof.Ed25519.X86_64.wideValue s₂ = fe s.mem (s.gpr .rsi) 0 +
      fe s.mem (s.gpr .rdx) 0 * fe s.mem (s.gpr .rcx) 0 := by
    rw [v₂, h₁.value, h₁.left, h₁.right]
  have base₂ : s₂.gpr .rdi = s.gpr .r8 := (k₂.1 _ (by decide)).trans h₁.base
  have wr₂ : s₂.wr = s.wr := k₂.2.2.2.trans h₁.wr
  apply WP.seq
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.storeWide_ok base₂ (wr₂ ▸ hw)) fun s₃ ⟨v₃, g₃, rd₃, wr₃, o₃⟩ => ?_
  have rdi₃ : s₃.gpr .rdi = s.gpr .r8 := (congrFun g₃ _).trans base₂
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.reduceArgs_ok rdi₃ (by rw [wr₃, wr₂]; exact hw))
    fun s₄ ⟨rsi₄, m₄, g₄, rd₄, wr₄⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarInit_ok s₄) fun s₅ ⟨b₅, v₅, k₅⟩ => ?_
  have rsi₅ : s₅.gpr .rsi = off (s.gpr .r8) 128 := by rw [k₅.1 _ (by decide), rsi₄]
  have rdi₅ : s₅.gpr .rdi = s.gpr .r8 := by rw [k₅.1 _ (by decide), g₄ _ (by decide), rdi₃]
  have mem₅ : s₅.mem = s₃.mem.writeW (off (s.gpr .r8) 48) (s₃.gpr .rbx) := by rw [k₅.2.1, m₄]
  have o₅ : Outside (s.gpr .r8) 48 8 s₃.mem s₅.mem := by
    rw [mem₅]; exact writeW_outside _ _ _ (by omega)
  have wr₅ : s₅.wr = s.wr := by rw [k₅.2.2.2, wr₄, wr₃, wr₂]
  have read₅ : ∀ k < 8, InRegions (s₅.rd ++ s₅.wr) (s₅.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8 := by
    intro k hk
    refine ⟨⟨s.gpr .r8, 8192⟩, List.mem_append_right _ (wr₅ ▸ hw), ?_⟩
    rw [rsi₅, Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
  have fm₅ : Frame [⟨s.gpr .r8, 8192⟩] s.mem s₅.mem := by
    have fm₂ : Frame [⟨s.gpr .r8, 8192⟩] s.mem s₂.mem := by rw [k₂.2.1]; exact h₁.frame
    exact (fm₂.trans (VG.Proof.Ed25519.X86_64.scratchFrame o₃ (by decide))).trans (VG.Proof.Ed25519.X86_64.scratchFrame o₅ (by decide))
  have sv₅ : Saved (s.gpr .r8) s.gpr s₅.mem := by
    have sv₂ : Saved (s.gpr .r8) s.gpr s₂.mem := by rw [k₂.2.1]; exact h₁.saved
    exact (sv₂.outside o₃ (by decide)).outside o₅ (by decide)
  have wide₅ : decodeLE (bytesAt s₅.mem (off (s.gpr .r8) 128) 64) = VG.Proof.Ed25519.X86_64.wideValue s₂ := by
    rw [VG.Proof.Ed25519.X86_64.decodeLE_wide, o₅.fe (by decide) (by decide), o₅.fe (by decide) (by decide), ← VG.Proof.Ed25519.X86_64.decodeLE_wide, v₃]
  apply WP.seq
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarLoop_ok s₅ b₅ v₅ read₅) fun s₆ ⟨v₆, k₆⟩ => ?_
  have wr₆ : s₆.wr = s.wr := k₆.2.2.2.trans wr₅
  have val₆ : VG.Proof.Ed25519.X86_64.scalarValue s₆ = (fe s.mem (s.gpr .rsi) 0 +
      fe s.mem (s.gpr .rdx) 0 * fe s.mem (s.gpr .rcx) 0) % Spec.Ed25519.L := by
    rw [v₆, rsi₅, wide₅, prod₂]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.finishArgs_ok ((k₆.1 _ (by decide)).trans rdi₅) (wr₆ ▸ hw))
    fun s₇ ⟨dx₇, di₇, g₇', m₇', rd₇', wr₇'⟩ => ?_
  have out₇ : s₇.gpr .rdi = s.gpr .rdi := by
    rw [di₇, k₆.2.1, mem₅, Mem.readW_writeW_self64, g₃, k₂.1 _ (by decide), h₁.out]
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarRestore_ok (g := s.gpr) dx₇ (by rw [wr₇', wr₆]; exact hw)
    (by rw [m₇', k₆.2.1]; exact sv₅)) fun s₈ ⟨rest₈, g₈, m₈, _, wr₈⟩ => ?_
  have rdi₈ : s₈.gpr .rdi = s.gpr .rdi := (g₈ _ (by decide)).trans out₇
  have hwo : (⟨s.gpr .rdi, 32⟩ : Region) ∈ s₈.wr := by rw [wr₈, wr₇', wr₆, hs.wr]; simp
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarOut_ok rdi₈ hwo) fun t ⟨mt, gt, _, _⟩ => ?_
  have fm₈ : Frame [⟨s.gpr .r8, 8192⟩] s.mem s₈.mem := by
    rw [m₈, m₇', k₆.2.1]; exact fm₅
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [gt]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rest₈ (.rbx, 0) (by decide)
    · exact rest₈ (.rbp, 8) (by decide)
    · rw [g₈ _ (by decide), g₇' _ (by decide) (by decide), k₆.1 _ (by decide), k₅.1 _ (by decide),
        g₄ _ (by decide), g₃, k₂.1 _ (by decide), h₁.rsp]
    · exact rest₈ (.r12, 16) (by decide)
    · exact rest₈ (.r13, 24) (by decide)
    · exact rest₈ (.r14, 32) (by decide)
    · exact rest₈ (.r15, 40) (by decide)
  · have ft : Frame [⟨s.gpr .r8, 8192⟩, ⟨s.gpr .rdi, 32⟩] s.mem t.mem := by
      rw [mt]
      have c : ∀ d, d + 8 ≤ 32 → (⟨s.gpr .rdi, 32⟩ : Region).Contains (off (s.gpr .rdi) d) (64 / 8) :=
        fun d hd => Offset.contains_base _ hd (by omega)
      have hm : (⟨s.gpr .rdi, 32⟩ : Region) ∈ [⟨s.gpr .r8, 8192⟩, ⟨s.gpr .rdi, 32⟩] := by simp
      exact ((((fm₈.mono (by simp)).writeW hm _ (c 0 (by decide))).writeW hm _
        (c 8 (by decide))).writeW hm _ (c 16 (by decide))).writeW hm _ (c 24 (by decide))
    exact ft.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hs.ret_sc
      · exact hs.ret_out) (by decide)
  · change bytesAt t.mem (s.gpr .rdi) 32 = Spec.Ed25519.scalarMulAdd _ _ _
    rw [mt]
    change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    rw [bytesAt_st4, Spec.Ed25519.scalarMulAdd, VG.Proof.Ed25519.X86_64.encodeLE_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    have v₈ : VG.Proof.Ed25519.X86_64.scalarValue s₈ = VG.Proof.Ed25519.X86_64.scalarValue s₆ := by
      simp only [VG.Proof.Ed25519.X86_64.scalarValue, g₈ .r8 (by decide), g₈ .r9 (by decide), g₈ .r10 (by decide),
        g₈ .r11 (by decide), g₇' .r8 (by decide) (by decide), g₇' .r9 (by decide) (by decide),
        g₇' .r10 (by decide) (by decide), g₇' .r11 (by decide) (by decide)]
    change VG.Proof.Ed25519.X86_64.scalarValue s₈ = _
    rw [v₈, val₆]
    have hd (p : Addr) : decodeLE (bytesAt s.mem p 32) = fe s.mem p 0 := by
      have h := VG.Proof.Ed25519.X86_64.decodeLE_words s.mem p 0
      rw [show off p 0 = p from BitVec.add_zero p] at h
      exact h
    rw [hd, hd, hd]

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.MulAddLit`. -/
section
/-! A checked code literal for the taint, ABI, and stack-pointer audits. -/

namespace VG

materialize_code Impl.Ed25519.X86_64.scalarMulAdd

end VG
end

/-! Scalar multiply-add satisfies the merged Ed25519 contract. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

def mulAddSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000
    | .r8 => 0x5000 | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x5000, 8192⟩]

theorem scalarMulAdd_ok (s : State) (hs : scalarMulAddLocal.pre s) :
    ∃ t s', Exec isa scalarMulAdd s t s' ∧ abiPreserved s s' ∧ scalarMulAddLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.Ed25519.X86_64.scalarMulAdd_correct (MulAddPre.of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

/-- The arguments are public, and so is what the code stores at `r8` (region 1),
the scratch: the output's address, at byte 48. -/
def scalarMulAddτ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8], flags := false, lens := [0, 8192],
    bases := [(.r8, 1, 0)] }

theorem scalarMulAdd_agree {s₁ s₂ : State} (h₁ : scalarMulAddLocal.pre s₁)
    (h₂ : scalarMulAddLocal.pre s₂) (hpub : scalarMulAddLocal.pub s₁ s₂) :
    X86_64.Taint.Agree VG.Proof.Ed25519.X86_64.scalarMulAddτ s₁ s₂ := by
  obtain ⟨-, p1, p2, p3, p4, p5⟩ := hpub
  have wf : ∀ s, scalarMulAddLocal.pre s → X86_64.Taint.Wf VG.Proof.Ed25519.X86_64.scalarMulAddτ s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, -, -, -, d⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, VG.Proof.Ed25519.X86_64.scalarMulAddτ], by simp [hw, d], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [VG.Proof.Ed25519.X86_64.scalarMulAddτ, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [VG.Proof.Ed25519.X86_64.scalarMulAddτ, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p5]
  · intro sl h; simp [VG.Proof.Ed25519.X86_64.scalarMulAddτ] at h
  · intro sl h; simp [VG.Proof.Ed25519.X86_64.scalarMulAddτ] at h

theorem scalarMulAdd_ct : ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) VG.Proof.Ed25519.X86_64.scalarMulAddτ
    (fun _ _ h₁ h₂ hp => VG.Proof.Ed25519.X86_64.scalarMulAdd_agree h₁ h₂ hp) (by taint_decide)

theorem scalarMulAdd_verified : Verified X86_64.target scalarMulAdd
    (Spec.Ed25519.scalarMulAddContract X86_64.abi) :=
  Verified.of_correct VG.Proof.Ed25519.X86_64.scalarMulAdd_ok VG.Proof.Ed25519.X86_64.scalarMulAdd_ct (by
    sig_implies [Spec.Ed25519.scalarMulAddContract, Spec.Ed25519.scalarMulAddSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, VG.Proof.Ed25519.X86_64.scalarMulAddLocal]
      [mulAddSatState] using VG.Proof.Ed25519.X86_64.mulAddSatState)

end VG.Proof.Ed25519.X86_64

end
