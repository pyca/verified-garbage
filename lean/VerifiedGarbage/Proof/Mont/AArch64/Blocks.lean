import VerifiedGarbage.Proof.Mont.AArch64.Row

/-!
# Montgomery arithmetic on AArch64: the small blocks of a round

Each run symbolically once, for any registers: a row with its carry word
cleared first (`mulRow`), the carry of a row into the two top words
(`carryUp`), and the computation of `u = t₀ m' mod 2⁶⁴` (`uBlock`).
-/

namespace VG.Proof.Mont.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut Word64.addCarry_value)

/-- `r = 0`. -/
theorem movz0_ok (s : State) (r : Reg) :
    WP isa (.block [.movz .x r 0 0]) s fun s' => s'.gpr r = 0 ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
    ite_true, RegUpd.gpr_write_self, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  exact RegUpd.gpr_write_of_ne _ _ _ hq

/-- A row, with the carry word cleared first. -/
theorem mulRow_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {ts : List Reg}
    {d : Nat} (hd : d + 8 * ts.length ≤ size) (ha : d % 8 = 0) (hz : s.gpr .x7 = 0) (hf : Fresh ts) :
    WP isa (.block (mulRow ts d)) s fun s' =>
      regsVal s' ts + 2 ^ (64 * ts.length) * (s'.gpr .x5).toNat =
        regsVal s ts + (s.gpr .x1).toNat * wordsVal s.mem base d ts.length ∧
      Keeps (.x5 :: .x2 :: .x3 :: .x4 :: ts) s s' := by
  rw [mulRow, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movz0_ok s .x5) fun s₁ ⟨b₁, k₁⟩ => ?_
  have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (by decide), hz]
  refine WP.mono (mulSteps_ok ts (hs.of_keeps k₁ (by decide)) hd ha hz₁ hf) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
    have := (hf.2 q hq)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
    exact this.2.2.2.2.2.1)
  rw [b₁, hR, k₁.mem, k₁.gpr .x1 (by decide)] at e₂
  refine ⟨by simpa using e₂, (k₁.mono (by sub_regs)).trans k₂⟩

/-- The carry word `x5` into `tn` and its carry into `tn1`, if that does not
overflow, with `x7 = 0`. -/
theorem carryUp_ok (s : State) {tn tn1 : Reg} (h1 : tn ≠ tn1) (hz : s.gpr .x7 = 0)
    (hn7 : tn ≠ .x7)
    (hb : (s.gpr tn).toNat + 2 ^ 64 * (s.gpr tn1).toNat + (s.gpr .x5).toNat < 2 ^ 128) :
    WP isa (.block (carryUp tn tn1)) s fun s' =>
      (s'.gpr tn).toNat + 2 ^ 64 * (s'.gpr tn1).toNat =
        (s.gpr tn).toNat + 2 ^ 64 * (s.gpr tn1).toNat + (s.gpr .x5).toNat ∧
      Keeps [tn, tn1] s s' := by
  apply WP.of_runBlock
  simp only [carryUp, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, h1, Ne.symm h1, Ne.symm hn7, hz,
    Bool.toNat_false, Option.some.injEq, exists_eq_left']
  dsimp only [Size.bits]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have e0 := Word64.addCarry_value (s.gpr tn) (s.gpr .x5) false
    have e1 := Word64.addCarry_value (s.gpr tn1) 0 (Word64.carryOut (s.gpr tn) (s.gpr .x5) false)
    have := Bool.toNat_le (Word64.carryOut (s.gpr tn1) 0 (Word64.carryOut (s.gpr tn) (s.gpr .x5) false))
    have hz' : (0 : BitVec 64).toNat = 0 := rfl
    simp only [Word64.addCarry, Word64.carryOut, Bool.toNat_false, hz', Nat.add_zero,
      BitVec.add_zero] at e0 e1 this ⊢
    have := (s.gpr tn1).isLt
    have hc : (decide (2 ^ 64 ≤ (s.gpr tn1).toNat +
        (decide (2 ^ 64 ≤ (s.gpr tn).toNat + (s.gpr .x5).toNat)).toNat)).toNat = 0 := by
      have := Bool.toNat_le (decide (2 ^ 64 ≤ (s.gpr tn).toNat + (s.gpr .x5).toNat))
      omega
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2, ite_false]

/-- `r = v`. -/
theorem const64_ok (s : State) (r : Reg) (v : BitVec 64) :
    WP isa (.block (const64 r v)) s fun t => t.gpr r = v ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [const64, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨movz_movk64' v, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r' hr
  have h : r' ≠ r := by simpa only [List.mem_singleton] using hr
  simp only [RegUpd.gpr_write_of_ne _ _ _ h]

/-- `x1 = t₀ m' mod 2⁶⁴`, with `m'` in `x6`. -/
theorem uBlock_ok (s : State) (t0 : Reg) (h6 : t0 ≠ .x6) (minv : BitVec 64) :
    WP isa (.block (const64 .x6 minv ++ [.mul .x .x1 t0 .x6])) s
      fun s' => (s'.gpr .x1).toNat = (s.gpr t0).toNat * minv.toNat % 2 ^ 64 ∧
        Keeps [.x1, .x6] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s .x6 minv) fun s₁ ⟨e₁, k₁⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, k₁.mem, k₁.rd, k₁.wr, k₁.sp⟩⟩
  · rw [BitVec.toNat_mul, e₁, k₁.gpr t0 (by simpa using h6)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_write_of_ne _ _ _ hr.1, k₁.gpr r (by simpa using hr.2)]

end VG.Proof.Mont.AArch64
