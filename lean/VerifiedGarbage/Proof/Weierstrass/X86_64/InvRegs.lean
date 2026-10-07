import VerifiedGarbage.Proof.Weierstrass.X86_64.InvWords
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Steps

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

end VG.Proof.Weierstrass.X86_64
