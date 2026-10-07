import VerifiedGarbage.Proof.Weierstrass.X86_64.InvWords
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Steps
import VerifiedGarbage.Proof.Mont.X86_64.MulPX
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Short Weierstrass curves on x86-64: the inversion's updates in registers

For four words with BMI2 and ADX (`InvCfg.updX`, `Impl/Weierstrass/X86_64/Inv.lean`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono add_carry adc_carry sub_borrow sbb_borrow)

/-! ## Loads through register writes -/

theorem load64_setReg (s : State) (r : Reg) (v : BitVec 64) (a : Addr) :
    (s.setReg r v).load64 a = s.load64 a := rfl
theorem load64_setFlags (s : State) (a b c d : Option Bool) (x : Addr) :
    (s.setFlags a b c d).load64 x = s.load64 x := rfl
theorem load64_arithFlags {w : Nat} (s : State) (x : BitVec w) (c o : Bool) (a : Addr) :
    (arithFlags s x c o).load64 a = s.load64 a := rfl

/-- `mulx`'s two words of a product. -/
theorem mulx_lohi (a b : BitVec 64) :
    (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat + 2 ^ 64 * (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat =
      a.toNat * b.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have h : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ / 2 ^ 64) (by omega)]
  omega

/-- The value of the accumulator `aRegs`. -/
abbrev aVal (s : State) : Nat := regsVal s aRegs

/-- `rowFirst`: the accumulator is `w [x]` (four or five words), modulo `2^320`. -/
theorem rowFirst5_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (w : Reg)
    {x : Nat} (hx : x + 40 ≤ size) :
    WP isa (.block (rowFirst true w x)) s fun t =>
      aVal t % 2 ^ 320 = (s.gpr w).toNat * wordsVal s.mem base x 5 % 2 ^ 320 ∧
      Keeps [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r13, .r15] s t := by
  have L : ∀ d, d + 8 ≤ size → s.load64 (off base d) = some (word s.mem base d) := fun d hd => by
    have := load_sc hs hd; rwa [ea_sc, hs.rdi] at this
  have L0 := L x (by omega); have L1 := L (x + 8) (by omega); have L2 := L (x + 16) (by omega)
  have L3 := L (x + 24) (by omega); have L4 := L (x + 32) (by omega)
  apply WP.of_runBlock
  simp only [rowFirst, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, execMulx, execAlu, readSrc, ea_sc, Option.map_some, Option.bind_some, load64_setReg, load64_arithFlags,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags, ↓reduceIte,
    hs.rdi, L0, L1, L2, L3, L4, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [aVal, aRegs, regsVal, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ↓reduceIte, reduceCtorEq]
    have m0 := mulx_lohi (s.gpr w) (Mont.word s.mem base x)
    have m1 := mulx_lohi (s.gpr w) (Mont.word s.mem base (x + 8))
    have m2 := mulx_lohi (s.gpr w) (Mont.word s.mem base (x + 16))
    have m3 := mulx_lohi (s.gpr w) (Mont.word s.mem base (x + 24))
    have m4 := mulx_lohi (s.gpr w) (Mont.word s.mem base (x + 32))
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base x).toNat) = l0 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base x).toNat / 2 ^ 64) = h0 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (x + 8)).toNat) = l1 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (x + 8)).toNat / 2 ^ 64) = h1 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (x + 16)).toNat) = l2 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (x + 16)).toNat / 2 ^ 64) = h2 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (x + 24)).toNat) = l3 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (x + 24)).toNat / 2 ^ 64) = h3 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (x + 32)).toNat) = l4 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (x + 32)).toNat / 2 ^ 64) = h4 at *
    have e1 := add_carry h0 l1
    generalize decide (2 ^ 64 ≤ h0.toNat + l1.toNat) = c1 at e1 ⊢
    have e2 := adc_carry h1 l2 c1
    generalize decide (2 ^ 64 ≤ h1.toNat + l2.toNat + c1.toNat) = c2 at e2 ⊢
    have e3 := adc_carry h2 l3 c2
    generalize decide (2 ^ 64 ≤ h2.toNat + l3.toNat + c2.toNat) = c3 at e3 ⊢
    have e4 := adc_carry h3 l4 c3
    generalize decide (2 ^ 64 ≤ h3.toNat + l4.toNat + c3.toNat) = c4 at e4 ⊢
    simp only [wordsVal, Nat.add_assoc, Nat.reduceAdd, Nat.mul_add, Nat.mul_zero, Nat.add_zero,
      Nat.mul_left_comm (s.gpr w).toNat]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨ra, rb, rc, rd, rbp, r8, r13, r15⟩ := hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ra, rb, rc, rd, rbp, r8, r13, r15, ite_false]

theorem of_setReg' (s : State) (r : Reg) (v : BitVec 64) : (s.setReg r v).of = s.of := rfl
theorem of_setFlags' (s : State) (a b c d : Option Bool) : (s.setFlags a b c d).of = b := rfl

/-- `rowAcc`: the accumulator plus `w [y]` (five words), modulo `2^320`. -/
theorem rowAcc5_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (w : Reg)
    {y : Nat} (hy : y + 40 ≤ size) :
    WP isa (.block (rowAcc true w y)) s fun t =>
      aVal t % 2 ^ 320 = (aVal s + (s.gpr w).toNat * wordsVal s.mem base y 5) % 2 ^ 320 ∧
      Keeps [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r13, .r15] s t := by
  have L : ∀ d, d + 8 ≤ size → s.load64 (off base d) = some (word s.mem base d) := fun d hd => by
    have := load_sc hs hd; rwa [ea_sc, hs.rdi] at this
  have L0 := L y (by omega); have L1 := L (y + 8) (by omega); have L2 := L (y + 16) (by omega)
  have L3 := L (y + 24) (by omega); have L4 := L (y + 32) (by omega)
  apply WP.of_runBlock
  simp only [rowAcc, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, execMulx, execAdcx, execAdox, execAlu32, readSrc, readSrc32, ea_sc, Option.map_some, Option.bind_some,
    State.setReg32, arithFlags, BitVec.xor_self, load64_setReg, load64_setFlags,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.cf_setReg, RegUpd.cf_setFlags, of_setReg', of_setFlags', ↓reduceIte,
    hs.rdi, L0, L1, L2, L3, L4, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [aVal, aRegs, regsVal, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ↓reduceIte, reduceCtorEq]
    have m0 := mulx_lohi (s.gpr w) (Mont.word s.mem base y)
    have m1 := mulx_lohi (s.gpr w) (Mont.word s.mem base (y + 8))
    have m2 := mulx_lohi (s.gpr w) (Mont.word s.mem base (y + 16))
    have m3 := mulx_lohi (s.gpr w) (Mont.word s.mem base (y + 24))
    have m4 := mulx_lohi (s.gpr w) (Mont.word s.mem base (y + 32))
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base y).toNat) = l0 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base y).toNat / 2 ^ 64) = h0 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (y + 8)).toNat) = l1 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (y + 8)).toNat / 2 ^ 64) = h1 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (y + 16)).toNat) = l2 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (y + 16)).toNat / 2 ^ 64) = h2 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (y + 24)).toNat) = l3 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (y + 24)).toNat / 2 ^ 64) = h3 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (y + 32)).toNat) = l4 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (y + 32)).toNat / 2 ^ 64) = h4 at *
    generalize s.gpr .rcx = a0 at *
    generalize s.gpr .rbp = a1 at *
    generalize s.gpr .r8 = a2 at *
    generalize s.gpr .r13 = a3 at *
    generalize s.gpr .r15 = a4 at *
    -- The OF chain (low halves) and the CF chain (high halves).
    have e1 := adc_carry a0 l0 false
    generalize decide (2 ^ 64 ≤ a0.toNat + l0.toNat + false.toNat) = o1 at e1 ⊢
    have e2 := adc_carry a1 h0 false
    generalize decide (2 ^ 64 ≤ a1.toNat + h0.toNat + false.toNat) = c1 at e2 ⊢
    generalize a1 + h0 + (BitVec.ofBool false).setWidth 64 = b1 at e2 ⊢
    have e3 := adc_carry b1 l1 o1
    generalize decide (2 ^ 64 ≤ b1.toNat + l1.toNat + o1.toNat) = o2 at e3 ⊢
    have e4 := adc_carry a2 h1 c1
    generalize decide (2 ^ 64 ≤ a2.toNat + h1.toNat + c1.toNat) = c2 at e4 ⊢
    generalize a2 + h1 + (BitVec.ofBool c1).setWidth 64 = b2 at e4 ⊢
    have e5 := adc_carry b2 l2 o2
    generalize decide (2 ^ 64 ≤ b2.toNat + l2.toNat + o2.toNat) = o3 at e5 ⊢
    have e6 := adc_carry a3 h2 c2
    generalize decide (2 ^ 64 ≤ a3.toNat + h2.toNat + c2.toNat) = c3 at e6 ⊢
    generalize a3 + h2 + (BitVec.ofBool c2).setWidth 64 = b3 at e6 ⊢
    have e7 := adc_carry b3 l3 o3
    generalize decide (2 ^ 64 ≤ b3.toNat + l3.toNat + o3.toNat) = o4 at e7 ⊢
    have e8 := adc_carry a4 h3 c3
    generalize decide (2 ^ 64 ≤ a4.toNat + h3.toNat + c3.toNat) = c4 at e8 ⊢
    generalize a4 + h3 + (BitVec.ofBool c3).setWidth 64 = b4 at e8 ⊢
    have e9 := adc_carry b4 l4 o4
    generalize decide (2 ^ 64 ≤ b4.toNat + l4.toNat + o4.toNat) = o5 at e9 ⊢
    simp only [wordsVal, Nat.add_assoc, Nat.reduceAdd, Nat.mul_add, Nat.mul_zero, Nat.add_zero,
      Nat.mul_left_comm (s.gpr w).toNat, Bool.toNat_false] at *
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨ra, rb, rc, rd, rbp, r8, r13, r15⟩ := hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ra, rb, rc, rd, rbp, r8, r13, r15, ite_false]

/-- `rowFirst` of four words: the accumulator is `w [x]`. -/
theorem rowFirst4_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (w : Reg)
    {x : Nat} (hx : x + 32 ≤ size) :
    WP isa (.block (rowFirst false w x)) s fun t =>
      aVal t % 2 ^ 320 = (s.gpr w).toNat * wordsVal s.mem base x 4 % 2 ^ 320 ∧
      Keeps [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r13, .r15] s t := by
  have L : ∀ d, d + 8 ≤ size → s.load64 (off base d) = some (word s.mem base d) := fun d hd => by
    have := load_sc hs hd; rwa [ea_sc, hs.rdi] at this
  have L0 := L x (by omega); have L1 := L (x + 8) (by omega); have L2 := L (x + 16) (by omega)
  have L3 := L (x + 24) (by omega)
  apply WP.of_runBlock
  simp only [rowFirst, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, execMulx, execAlu, readSrc, ea_sc, Option.map_some, Option.bind_some, load64_setReg, load64_arithFlags,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags, ↓reduceIte,
    hs.rdi, L0, L1, L2, L3, reduceCtorEq, Bool.false_eq_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [aVal, aRegs, regsVal, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ↓reduceIte, reduceCtorEq]
    have m0 := mulx_lohi (s.gpr w) (Mont.word s.mem base x)
    have m1 := mulx_lohi (s.gpr w) (Mont.word s.mem base (x + 8))
    have m2 := mulx_lohi (s.gpr w) (Mont.word s.mem base (x + 16))
    have m3 := mulx_lohi (s.gpr w) (Mont.word s.mem base (x + 24))
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base x).toNat) = l0 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base x).toNat / 2 ^ 64) = h0 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (x + 8)).toNat) = l1 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (x + 8)).toNat / 2 ^ 64) = h1 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (x + 16)).toNat) = l2 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (x + 16)).toNat / 2 ^ 64) = h2 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (x + 24)).toNat) = l3 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (x + 24)).toNat / 2 ^ 64) = h3 at *
    have e1 := add_carry h0 l1
    generalize decide (2 ^ 64 ≤ h0.toNat + l1.toNat) = c1 at e1 ⊢
    have e2 := adc_carry h1 l2 c1
    generalize decide (2 ^ 64 ≤ h1.toNat + l2.toNat + c1.toNat) = c2 at e2 ⊢
    have e3 := adc_carry h2 l3 c2
    generalize decide (2 ^ 64 ≤ h2.toNat + l3.toNat + c2.toNat) = c3 at e3 ⊢
    have e4 := adc_carry h3 (BitVec.signExtend 64 (0 : BitVec 32)) c3
    rw [VG.Proof.X25519.X86_64.se0] at e4 ⊢
    generalize decide (2 ^ 64 ≤ h3.toNat + (0 : BitVec 64).toNat + c3.toNat) = c4 at e4 ⊢
    have z : (0 : BitVec 64).toNat = 0 := rfl
    rw [z] at e4
    simp only [wordsVal, Nat.add_assoc, Nat.reduceAdd, Nat.mul_add, Nat.mul_zero, Nat.add_zero,
      Nat.mul_left_comm (s.gpr w).toNat]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨ra, rb, rc, rd, rbp, r8, r13, r15⟩ := hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ra, rc, rd, rbp, r8, r13, r15, ite_false]

/-- `rowAcc` of four words: the accumulator plus `w [y]`, modulo `2^320`. -/
theorem rowAcc4_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (w : Reg)
    {y : Nat} (hy : y + 32 ≤ size) :
    WP isa (.block (rowAcc false w y)) s fun t =>
      aVal t % 2 ^ 320 = (aVal s + (s.gpr w).toNat * wordsVal s.mem base y 4) % 2 ^ 320 ∧
      Keeps [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r13, .r15] s t := by
  have L : ∀ d, d + 8 ≤ size → s.load64 (off base d) = some (word s.mem base d) := fun d hd => by
    have := load_sc hs hd; rwa [ea_sc, hs.rdi] at this
  have L0 := L y (by omega); have L1 := L (y + 8) (by omega); have L2 := L (y + 16) (by omega)
  have L3 := L (y + 24) (by omega)
  apply WP.of_runBlock
  simp only [rowAcc, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, execMulx, execAdcx, execAdox, execAlu32, readSrc, readSrc32, ea_sc, Option.map_some, Option.bind_some,
    State.setReg32, arithFlags, BitVec.xor_self, load64_setReg, load64_setFlags,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.cf_setReg, RegUpd.cf_setFlags, of_setReg', of_setFlags', ↓reduceIte,
    hs.rdi, L0, L1, L2, L3, reduceCtorEq, Bool.false_eq_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [aVal, aRegs, regsVal, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ↓reduceIte, reduceCtorEq]
    have m0 := mulx_lohi (s.gpr w) (Mont.word s.mem base y)
    have m1 := mulx_lohi (s.gpr w) (Mont.word s.mem base (y + 8))
    have m2 := mulx_lohi (s.gpr w) (Mont.word s.mem base (y + 16))
    have m3 := mulx_lohi (s.gpr w) (Mont.word s.mem base (y + 24))
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base y).toNat) = l0 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base y).toNat / 2 ^ 64) = h0 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (y + 8)).toNat) = l1 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (y + 8)).toNat / 2 ^ 64) = h1 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (y + 16)).toNat) = l2 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (y + 16)).toNat / 2 ^ 64) = h2 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (y + 24)).toNat) = l3 at *
    generalize BitVec.ofNat 64 ((s.gpr w).toNat * (Mont.word s.mem base (y + 24)).toNat / 2 ^ 64) = h3 at *
    generalize s.gpr .rcx = a0 at *
    generalize s.gpr .rbp = a1 at *
    generalize s.gpr .r8 = a2 at *
    generalize s.gpr .r13 = a3 at *
    generalize s.gpr .r15 = a4 at *
    -- The OF chain (low halves) and the CF chain (high halves).
    have e1 := adc_carry a0 l0 false
    generalize decide (2 ^ 64 ≤ a0.toNat + l0.toNat + false.toNat) = o1 at e1 ⊢
    have e2 := adc_carry a1 h0 false
    generalize decide (2 ^ 64 ≤ a1.toNat + h0.toNat + false.toNat) = c1 at e2 ⊢
    generalize a1 + h0 + (BitVec.ofBool false).setWidth 64 = b1 at e2 ⊢
    have e3 := adc_carry b1 l1 o1
    generalize decide (2 ^ 64 ≤ b1.toNat + l1.toNat + o1.toNat) = o2 at e3 ⊢
    have e4 := adc_carry a2 h1 c1
    generalize decide (2 ^ 64 ≤ a2.toNat + h1.toNat + c1.toNat) = c2 at e4 ⊢
    generalize a2 + h1 + (BitVec.ofBool c1).setWidth 64 = b2 at e4 ⊢
    have e5 := adc_carry b2 l2 o2
    generalize decide (2 ^ 64 ≤ b2.toNat + l2.toNat + o2.toNat) = o3 at e5 ⊢
    have e6 := adc_carry a3 h2 c2
    generalize decide (2 ^ 64 ≤ a3.toNat + h2.toNat + c2.toNat) = c3 at e6 ⊢
    generalize a3 + h2 + (BitVec.ofBool c2).setWidth 64 = b3 at e6 ⊢
    have e7 := adc_carry b3 l3 o3
    generalize decide (2 ^ 64 ≤ b3.toNat + l3.toNat + o3.toNat) = o4 at e7 ⊢
    have e8 := adc_carry a4 h3 c3
    generalize decide (2 ^ 64 ≤ a4.toNat + h3.toNat + c3.toNat) = c4 at e8 ⊢
    generalize a4 + h3 + (BitVec.ofBool c3).setWidth 64 = b4 at e8 ⊢
    have z : BitVec.setWidth 64 (0 : BitVec 32) = 0 := by decide
    rw [z] at *
    have e9 := adc_carry b4 0 o4
    generalize decide (2 ^ 64 ≤ b4.toNat + (0 : BitVec 64).toNat + o4.toNat) = o5 at e9 ⊢
    have z' : (0 : BitVec 64).toNat = 0 := rfl
    rw [z'] at e9
    simp only [wordsVal, Nat.add_assoc, Nat.reduceAdd, Nat.mul_add, Nat.mul_zero, Nat.add_zero,
      Nat.mul_left_comm (s.gpr w).toNat, Bool.toNat_false] at *
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨ra, rb, rc, rd, rbp, r8, r13, r15⟩ := hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ra, rb, rc, rd, rbp, r8, r13, r15, ite_false]


/-- `corr`: the accumulator less `2^64 [x]` (four words) if `w` is negative, modulo `2^320`. -/
theorem corr_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (w : Reg)
    {x : Nat} (hx : x + 32 ≤ size) :
    WP isa (.block (corr w x)) s fun t =>
      (aVal t + 2 ^ 64 * ((s.gpr w).toNat / 2 ^ 63 * wordsVal s.mem base x 4)) % 2 ^ 320 = aVal s % 2 ^ 320 ∧
      t.gpr .rcx = s.gpr .rcx ∧ Keeps [.rax, .rbx, .rdx, .rbp, .r8, .r13, .r15] s t := by
  have L : ∀ d, d + 8 ≤ size → s.load64 (off base d) = some (word s.mem base d) := fun d hd => by
    have := load_sc hs hd; rwa [ea_sc, hs.rdi] at this
  have L0 := L x (by omega); have L1 := L (x + 8) (by omega); have L2 := L (x + 16) (by omega)
  have L3 := L (x + 24) (by omega)
  apply WP.of_runBlock
  simp only [corr, runBlock_cons, runStep_some, runBlock_nil, Nat.reduceLeDiff, Nat.reduceEqDiff, and_self,
    exec, execMulx, execAlu, execShift, readSrc, ea_sc, Option.map_some, Option.bind_some, load64_setReg,
    load64_setFlags, load64_arithFlags, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    RegUpd.cf_setReg, RegUpd.cf_arithFlags, ↓reduceIte,
    hs.rdi, L0, L1, L2, L3, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [aVal, aRegs, regsVal, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, ↓reduceIte,
      reduceCtorEq]
    generalize hb : s.gpr w >>> 63 = b
    have hb1 : b.toNat = (s.gpr w).toNat / 2 ^ 63 := by
      rw [← hb, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hb2 : b.toNat ≤ 1 := by have := (s.gpr w).isLt; omega
    have m0 := mulx_lohi b (Mont.word s.mem base x)
    have m1 := mulx_lohi b (Mont.word s.mem base (x + 8))
    have m2 := mulx_lohi b (Mont.word s.mem base (x + 16))
    have m3 := mulx_lohi b (Mont.word s.mem base (x + 24))
    have q0 := Nat.mul_le_mul_right (Mont.word s.mem base x).toNat hb2
    have q1 := Nat.mul_le_mul_right (Mont.word s.mem base (x + 8)).toNat hb2
    have q2 := Nat.mul_le_mul_right (Mont.word s.mem base (x + 16)).toNat hb2
    have q3 := Nat.mul_le_mul_right (Mont.word s.mem base (x + 24)).toNat hb2
    have x0 := (Mont.word s.mem base x).isLt; have x1 := (Mont.word s.mem base (x + 8)).isLt
    have x2 := (Mont.word s.mem base (x + 16)).isLt; have x3 := (Mont.word s.mem base (x + 24)).isLt
    generalize BitVec.ofNat 64 (b.toNat * (Mont.word s.mem base x).toNat) = l0 at *
    generalize BitVec.ofNat 64 (b.toNat * (Mont.word s.mem base x).toNat / 2 ^ 64) = h0 at *
    generalize BitVec.ofNat 64 (b.toNat * (Mont.word s.mem base (x + 8)).toNat) = l1 at *
    generalize BitVec.ofNat 64 (b.toNat * (Mont.word s.mem base (x + 8)).toNat / 2 ^ 64) = h1 at *
    generalize BitVec.ofNat 64 (b.toNat * (Mont.word s.mem base (x + 16)).toNat) = l2 at *
    generalize BitVec.ofNat 64 (b.toNat * (Mont.word s.mem base (x + 16)).toNat / 2 ^ 64) = h2 at *
    generalize BitVec.ofNat 64 (b.toNat * (Mont.word s.mem base (x + 24)).toNat) = l3 at *
    generalize BitVec.ofNat 64 (b.toNat * (Mont.word s.mem base (x + 24)).toNat / 2 ^ 64) = h3 at *
    have e1 := sub_borrow (s.gpr .rbp) l0
    generalize decide ((s.gpr .rbp).toNat < l0.toNat) = c1 at e1 ⊢
    have e2 := sbb_borrow (s.gpr .r8) l1 c1
    generalize decide ((s.gpr .r8).toNat < l1.toNat + c1.toNat) = c2 at e2 ⊢
    have e3 := sbb_borrow (s.gpr .r13) l2 c2
    generalize decide ((s.gpr .r13).toNat < l2.toNat + c2.toNat) = c3 at e3 ⊢
    have e4 := sbb_borrow (s.gpr .r15) l3 c3
    generalize decide ((s.gpr .r15).toNat < l3.toNat + c3.toNat) = c4 at e4 ⊢
    rw [← hb1]
    simp only [wordsVal, Nat.add_assoc, Nat.reduceAdd, Nat.mul_add, Nat.mul_zero, Nat.add_zero,
      Nat.mul_left_comm b.toNat]
    simp only [Nat.one_mul] at q0 q1 q2 q3
    omega
  · trivial
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨ra, rb, rd, rbp, r8, r13, r15⟩ := hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, ra, rb, rd, rbp, r8, r13, r15,
      ite_false]

/-! ## The signed combination -/

/-- The registers `linX` writes. -/
abbrev clobX : List Reg := [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r13, .r15]

/-- The rows and the corrections as the signed combination modulo `2^320`, given
that `2^64 X ≡ 2^64 X₄` (the corrections' four words of `X`). -/
theorem lin_int {A1 A2 A3 A4 W W' X X4 Y Y4 : Nat} (hW : W < 2 ^ 64) (hW' : W' < 2 ^ 64)
    (hX : 2 ^ 64 * X % 2 ^ 320 = 2 ^ 64 * X4 % 2 ^ 320) (hY : 2 ^ 64 * Y % 2 ^ 320 = 2 ^ 64 * Y4 % 2 ^ 320)
    (e1 : A1 % 2 ^ 320 = W * X % 2 ^ 320) (e2 : A2 % 2 ^ 320 = (A1 + W' * Y) % 2 ^ 320)
    (e3 : (A3 + 2 ^ 64 * (W / 2 ^ 63 * X4)) % 2 ^ 320 = A2 % 2 ^ 320)
    (e4 : (A4 + 2 ^ 64 * (W' / 2 ^ 63 * Y4)) % 2 ^ 320 = A3 % 2 ^ 320) :
    (A4 : Int) % ((2 ^ 320 : Nat) : Int) = (((W : Int) - (if 2 ^ 63 ≤ W then 2 ^ 64 else 0)) * X +
      ((W' : Int) - (if 2 ^ 63 ≤ W' then 2 ^ 64 else 0)) * Y) % ((2 ^ 320 : Nat) : Int) := by
  have hb : ∀ V : Nat, V < 2 ^ 64 → (2 ^ 63 ≤ V ∧ V / 2 ^ 63 = 1) ∨ (V < 2 ^ 63 ∧ V / 2 ^ 63 = 0) :=
    fun V hV => by omega
  -- In `Nat`, with the corrections for the whole numbers.
  have hN : (A4 + 2 ^ 64 * (W / 2 ^ 63 * X) + 2 ^ 64 * (W' / 2 ^ 63 * Y)) % 2 ^ 320 =
      (W * X + W' * Y) % 2 ^ 320 := by
    rcases hb W hW with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rcases hb W' hW' with ⟨-, h4⟩ | ⟨-, h4⟩ <;>
      simp only [h2, h4, Nat.one_mul, Nat.zero_mul, Nat.mul_zero, Nat.add_zero] at e3 e4 ⊢ <;>
      generalize W * X = P at * <;> generalize W' * Y = Q at * <;> omega
  have hc : ∀ V : Nat, V < 2 ^ 64 →
      ((if 2 ^ 63 ≤ V then 2 ^ 64 else 0) : Int) = 2 ^ 64 * ((V / 2 ^ 63 : Nat) : Int) := fun V hV => by
    rcases hb V hV with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [h1, ite_true, h2, Nat.cast_one, Int.mul_one]
    · simp only [Nat.not_le_of_lt h1, ite_false, h2, Nat.cast_zero, Int.mul_zero]
  rw [hc W hW, hc W' hW']
  generalize (2 ^ 320 : Nat) = M at hN ⊢
  generalize W / 2 ^ 63 = b at hN ⊢
  generalize W' / 2 ^ 63 = b' at hN ⊢
  have h := congrArg (Nat.cast : Nat → Int) hN
  simp only [Int.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  have h' : Int.ModEq M ((A4 : Int) + (2 ^ 64 * (b * X) + 2 ^ 64 * (b' * Y)))
      ((W : Int) * X + (W' : Int) * Y) := by
    unfold Int.ModEq; rw [← h, Int.add_assoc]
  have := h'.sub_right (2 ^ 64 * ((b : Int) * X) + 2 ^ 64 * ((b' : Int) * Y))
  rw [Int.add_sub_cancel] at this
  unfold Int.ModEq at this
  rw [this]
  congr 1
  ring

/-- `linX` of five words: `u [x] + v [y]` modulo `2^320` (signed `u`, `v`). -/
theorem linX5_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w w' : Reg}
    (hw : w ∉ clobX) (hw' : w' ∉ clobX) {x y : Nat} (hx : x + 40 ≤ size) (hy : y + 40 ≤ size) :
    WP isa (.block (linX true w w' x y)) s fun t =>
      (aVal t : Int) % ((2 ^ 320 : Nat) : Int) = ((s.gpr w).toInt * wordsVal s.mem base x 5 +
        (s.gpr w').toInt * wordsVal s.mem base y 5) % ((2 ^ 320 : Nat) : Int) ∧ Keeps clobX s t := by
  rw [linX, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (rowFirst5_ok hs w hx) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (rowAcc5_ok hs₁ w' hy) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (corr_ok hs₂ w (x := x) (by omega)) fun s₃ ⟨e₃, _, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (corr_ok hs₃ w' (x := y) (by omega)) fun t ⟨e₄, _, k₄⟩ =>
    ⟨?_, ((k₁.trans k₂).trans (k₃.mono (by decide))).trans (k₄.mono (by decide))⟩
  have g1 : s₁.gpr w' = s.gpr w' := k₁.1 _ hw'
  have g2 : s₂.gpr w = s.gpr w := (k₂.1 _ hw).trans (k₁.1 _ hw)
  have g3 : s₃.gpr w' = s.gpr w' := (k₃.1 _ (fun h => hw' ((by decide :
      ∀ r ∈ ([.rax, .rbx, .rdx, .rbp, .r8, .r13, .r15] : List Reg), r ∈ clobX) _ h))).trans
    ((k₂.1 _ hw').trans g1)
  have M1 : s₁.mem = s.mem := k₁.2.1
  have M2 : s₂.mem = s.mem := k₂.2.1.trans M1
  have M3 : s₃.mem = s.mem := k₃.2.1.trans M2
  rw [g1, M1] at e₂
  rw [g2, M2] at e₃
  rw [g3, M3] at e₄
  rw [← Divstep.toInt_sgn, ← Divstep.toInt_sgn]
  have hX := wordsVal_succ_last s.mem base x 4
  have hY := wordsVal_succ_last s.mem base y 4
  refine lin_int (s.gpr w).isLt (s.gpr w').isLt ?_ ?_ e₁ e₂ e₃ e₄
  · rw [hX]; omega
  · rw [hY]; omega

/-- `linX` of four words: `u [x] + v [y]` modulo `2^320` (signed `u`, `v`). -/
theorem linX4_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w w' : Reg}
    (hw : w ∉ clobX) (hw' : w' ∉ clobX) {x y : Nat} (hx : x + 32 ≤ size) (hy : y + 32 ≤ size) :
    WP isa (.block (linX false w w' x y)) s fun t =>
      (aVal t : Int) % ((2 ^ 320 : Nat) : Int) = ((s.gpr w).toInt * wordsVal s.mem base x 4 +
        (s.gpr w').toInt * wordsVal s.mem base y 4) % ((2 ^ 320 : Nat) : Int) ∧ Keeps clobX s t := by
  rw [linX, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (rowFirst4_ok hs w hx) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (rowAcc4_ok hs₁ w' hy) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (corr_ok hs₂ w (x := x) hx) fun s₃ ⟨e₃, _, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (corr_ok hs₃ w' (x := y) hy) fun t ⟨e₄, _, k₄⟩ =>
    ⟨?_, ((k₁.trans k₂).trans (k₃.mono (by decide))).trans (k₄.mono (by decide))⟩
  have g1 : s₁.gpr w' = s.gpr w' := k₁.1 _ hw'
  have g2 : s₂.gpr w = s.gpr w := (k₂.1 _ hw).trans (k₁.1 _ hw)
  have g3 : s₃.gpr w' = s.gpr w' := (k₃.1 _ (fun h => hw' ((by decide :
      ∀ r ∈ ([.rax, .rbx, .rdx, .rbp, .r8, .r13, .r15] : List Reg), r ∈ clobX) _ h))).trans
    ((k₂.1 _ hw').trans g1)
  have M1 : s₁.mem = s.mem := k₁.2.1
  have M2 : s₂.mem = s.mem := k₂.2.1.trans M1
  have M3 : s₃.mem = s.mem := k₃.2.1.trans M2
  rw [g1, M1] at e₂
  rw [g2, M2] at e₃
  rw [g3, M3] at e₄
  rw [← Divstep.toInt_sgn, ← Divstep.toInt_sgn]
  exact lin_int (s.gpr w).isLt (s.gpr w').isLt rfl rfl e₁ e₂ e₃ e₄

end VG.Proof.Weierstrass.X86_64
