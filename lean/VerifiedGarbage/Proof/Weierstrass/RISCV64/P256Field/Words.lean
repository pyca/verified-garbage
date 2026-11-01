module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P256Field
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-!
# P-256's field on RISC-V: sums of words with `sltu` carries

The pieces of the reduction, the sums and the final subtraction of
`Impl/Weierstrass/RISCV64/P256Field.lean`, each a short block on registers
named by its arguments, as a sum of numbers (`toNat`) that changes only the
registers it writes (`Keeps`):

* `adc_ok`: `d + 2⁶⁴ c := x + y + c` (`add`, `sltu`, `add`, `sltu`, `add`);
* `sbb_ok`: `d - 2⁶⁴ c := x - y - c` (`sltu`, `sub`, `sltu`, `sub`, `add`);
* `add1_ok`, `add3s_ok`, `addTop_ok`: the shorter sums of a round, whose
  operands are small enough not to carry twice;
* `quot_ok`: the words of `q 2³²` and `q (2⁶⁴ - 2³² + 1)`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P256Field

open VG VG.RISCV64 VG.RISCV64.Wide

/-- P-256's prime. -/
abbrev P : Nat := 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1

variable {s : State}

/-- The value of a word written by `sltu`. -/
theorem sltu_le (c : Prop) [Decidable c] : (if c then (1 : BitVec 64) else 0).toNat ≤ 1 :=
  carry_le c

/-- One register written. -/
theorem upd_keeps {s' : State} {d : Reg} {v : BitVec 64} (u : Steps.Upd s s' d v) : Keeps [d] s s' :=
  ⟨fun r hr => u.other r (by simpa using hr), u.mem, u.rd, u.wr, u.sp⟩

/-- `li d, -1`. -/
theorem wp_lim1 {is : List Instr} {Q : State → Prop} {d : Reg}
    (k : ∀ s', Steps.Upd s s' d (BitVec.allOnes 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.li d (-1) :: is)) s Q := by
  refine Steps.WP.cons (exec_li (by decide)) ?_
  exact k _ (Steps.Upd.write _ _ _)

/-- A difference of words and its borrow. -/
theorem sub_borrow (x y : BitVec 64) :
    (x - y).toNat + y.toNat = x.toNat + 2 ^ 64 * (if x.toNat < y.toNat then 1 else 0) := by
  have := x.isLt; have := y.isLt
  rw [BitVec.toNat_sub]
  split <;> omega

/-- The value `sltu` writes. -/
theorem sltu_toNat (a b : BitVec 64) :
    (if a < b then (1 : BitVec 64) else 0).toNat = if a.toNat < b.toNat then 1 else 0 := by
  by_cases h : a < b
  · have h' : a.toNat < b.toNat := BitVec.lt_def.mp h
    simp only [h, h', ↓reduceIte]; rfl
  · have h' : ¬ a.toNat < b.toNat := fun h' => h (BitVec.lt_def.mpr h')
    simp only [h, h', ↓reduceIte]; rfl

set_option linter.unusedSimpArgs false in
/-- `d + 2⁶⁴ c := x + y + c`, through `u`, for a carry in `c ≤ 1`. -/
theorem adc_ok {d x y c u : Reg} (hdy : d ≠ y := by decide) (hdc : d ≠ c := by decide)
    (hud : u ≠ d := by decide) (huc : u ≠ c := by decide) :
    WP isa (.block [.add d x y, .sltu u d y, .add d d c, .sltu c d c, .add c c u]) s fun s' =>
      ((s.gpr c).toNat ≤ 1 →
        (s'.gpr d).toNat + 2 ^ 64 * (s'.gpr c).toNat = (s.gpr x).toNat + (s.gpr y).toNat + (s.gpr c).toNat) ∧
      Keeps [d, u, c] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu,
    RegUpd.gpr_write, hdy, hdc, hud, huc, Ne.symm hdy, Ne.symm hdc, Ne.symm hud,
    Ne.symm huc, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨fun hc => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have c₀ := carry (s.gpr x) (s.gpr y)
    have l₀ := carry_le (s.gpr x + s.gpr y < s.gpr y)
    generalize (if s.gpr x + s.gpr y < s.gpr y then (1 : BitVec 64) else 0) = k₀ at *
    have c₁ := carry (s.gpr x + s.gpr y) (s.gpr c)
    have l₁ := carry_le (s.gpr x + s.gpr y + s.gpr c < s.gpr c)
    generalize (if s.gpr x + s.gpr y + s.gpr c < s.gpr c then (1 : BitVec 64) else 0) = k₁ at *
    have hx := (s.gpr x).isLt
    have hy := (s.gpr y).isLt
    have hs := (s.gpr x + s.gpr y + s.gpr c).isLt
    have hk : k₁.toNat + k₀.toNat ≤ 1 := by omega
    rw [BitVec.toNat_add k₁ k₀, Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

set_option linter.unusedSimpArgs false in
/-- `d := x - y - c` and the borrow out into `c` (`d + y + c = x + 2⁶⁴ c'`),
through `u` and `v`, for a borrow in `c ≤ 1`. -/
theorem sbb_ok {d x y c u v : Reg} (hdc : d ≠ c := by decide)
    (hud : u ≠ d := by decide) (huc : u ≠ c := by decide) (hvd : v ≠ d := by decide)
    (hvc : v ≠ c := by decide) (huv : u ≠ v := by decide) (hux : u ≠ x := by decide)
    (huy : u ≠ y := by decide) :
    WP isa (.block [.sltu u x y, .sub d x y, .sltu v d c, .sub d d c, .add c u v]) s fun s' =>
      ((s.gpr c).toNat ≤ 1 →
        (s'.gpr d).toNat + (s.gpr y).toNat + (s.gpr c).toNat = (s.gpr x).toNat + 2 ^ 64 * (s'.gpr c).toNat ∧
        (s'.gpr c).toNat ≤ 1) ∧
      Keeps [d, u, v, c] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sub, exec_sltu,
    RegUpd.gpr_write, hdc, hud, huc, hvd, hvc, huv, hux, huy, Ne.symm hdc,
    Ne.symm hud, Ne.symm huc, Ne.symm hvd, Ne.symm hvc, Ne.symm huv, Ne.symm hux, Ne.symm huy, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨fun hc => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have hx := (s.gpr x).isLt
    have hy := (s.gpr y).isLt
    have e₁ : (s.gpr x - s.gpr y).toNat = ((s.gpr x).toNat + 2 ^ 64 - (s.gpr y).toNat) % 2 ^ 64 := by
      rw [BitVec.toNat_sub]; omega
    have e₂ : (s.gpr x - s.gpr y - s.gpr c).toNat =
        ((s.gpr x - s.gpr y).toNat + 2 ^ 64 - (s.gpr c).toNat) % 2 ^ 64 := by
      rw [BitVec.toNat_sub]; omega
    have b₁ := sltu_toNat (s.gpr x) (s.gpr y)
    have b₂ := sltu_toNat (s.gpr x - s.gpr y) (s.gpr c)
    rw [BitVec.toNat_add, b₁, b₂, e₂, e₁]
    split <;> split <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

set_option linter.unusedSimpArgs false in
/-- `d + 2⁶⁴ c := d + y`. -/
theorem add1_ok {d y c : Reg} (hdy : d ≠ y := by decide) (hdc : d ≠ c := by decide) :
    WP isa (.block [.add d d y, .sltu c d y]) s fun s' =>
      (s'.gpr d).toNat + 2 ^ 64 * (s'.gpr c).toNat = (s.gpr d).toNat + (s.gpr y).toNat ∧
      Keeps [d, c] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu,
    RegUpd.gpr_write, hdy, hdc, Ne.symm hdy, Ne.symm hdc, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨carry _ _, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

set_option linter.unusedSimpArgs false in
/-- `d + 2⁶⁴ c := d + y + c`, through `y`, for `y + c` below `2⁶⁴`. -/
theorem add3s_ok {d y c : Reg} (hdy : d ≠ y := by decide) (hdc : d ≠ c := by decide) :
    WP isa (.block [.add y y c, .add d d y, .sltu c d y]) s fun s' =>
      ((s.gpr y).toNat + (s.gpr c).toNat < 2 ^ 64 →
        (s'.gpr d).toNat + 2 ^ 64 * (s'.gpr c).toNat = (s.gpr d).toNat + (s.gpr y).toNat + (s.gpr c).toNat) ∧
      Keeps [d, y, c] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu,
    RegUpd.gpr_write, hdy, hdc, Ne.symm hdy, Ne.symm hdc, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun h => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have := carry (s.gpr d) (s.gpr y + s.gpr c)
    rw [BitVec.toNat_add (s.gpr y), Nat.mod_eq_of_lt h] at this
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

set_option linter.unusedSimpArgs false in
/-- `d + 2⁶⁴ k := d + h + c + k`, through `h`, for `h + c + k` below `2⁶⁴`. -/
theorem addTop_ok {d h c k : Reg} (hdh : d ≠ h := by decide)
    (hdk : d ≠ k := by decide) (hhk : h ≠ k := by decide) :
    WP isa (.block [.add h h c, .add h h k, .add d d h, .sltu k d h]) s fun s' =>
      ((s.gpr h).toNat + (s.gpr c).toNat + (s.gpr k).toNat < 2 ^ 64 →
        (s'.gpr d).toNat + 2 ^ 64 * (s'.gpr k).toNat =
          (s.gpr d).toNat + (s.gpr h).toNat + (s.gpr c).toNat + (s.gpr k).toNat) ∧
      Keeps [d, h, k] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu,
    RegUpd.gpr_write, hdh, hdk, hhk, Ne.symm hdh, Ne.symm hdk,
    Ne.symm hhk, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨fun hb => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have := carry (s.gpr d) (s.gpr h + s.gpr c + s.gpr k)
    have e : (s.gpr h + s.gpr c + s.gpr k).toNat = (s.gpr h).toNat + (s.gpr c).toNat + (s.gpr k).toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_add]; omega
    rw [e] at this
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- `q 2³²` in two words. -/
theorem shl_shr (q : BitVec 64) : (q <<< 32).toNat + 2 ^ 64 * (q >>> 32).toNat = q.toNat * 2 ^ 32 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := q.isLt
  omega

set_option linter.unusedSimpArgs false in
/-- `quot`: `a4 + 2⁶⁴ a5 = q 2³²` and `a6 + 2⁶⁴ a7 = q (2⁶⁴ - 2³² + 1)` for `q` in `r`,
with `a5 < 2³²` and `a7 ≤ 2⁶⁴ - 2³²`. -/
theorem quot_ok {r : Reg} (h4 : r ≠ .a4 := by decide) (h5 : r ≠ .a5 := by decide)
    (h6 : r ≠ .a6 := by decide) (h7 : r ≠ .a7 := by decide) :
    WP isa (.block [.shift .sll .d .a4 r 32, .shift .srl .d .a5 r 32, .sub .a6 r .a4,
        .sltu .a7 r .a4, .sub .t0 r .a5, .sub .a7 .t0 .a7]) s fun s' =>
      (s'.gpr .a4).toNat + 2 ^ 64 * (s'.gpr .a5).toNat = (s.gpr r).toNat * 2 ^ 32 ∧
      (s'.gpr .a6).toNat + 2 ^ 64 * (s'.gpr .a7).toNat = (s.gpr r).toNat * (2 ^ 64 - 2 ^ 32 + 1) ∧
      (s'.gpr .a5).toNat < 2 ^ 32 ∧ (s'.gpr .a7).toNat ≤ 2 ^ 64 - 2 ^ 32 ∧
      Keeps [.a4, .a5, .a6, .a7, .t0] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sub, exec_sltu,
    exec_shift_d (show 32 < 64 by decide), RegUpd.gpr_write, h4, h5, h6, h7, Ne.symm h4,
    Ne.symm h5, Ne.symm h6, Ne.symm h7, ite_true, ite_false, Option.some.injEq,
    exists_eq_left', show Reg.a4 ≠ Reg.a5 by decide, show Reg.a5 ≠ Reg.a4 by decide,
    show Reg.a6 ≠ Reg.a7 by decide, show Reg.a7 ≠ Reg.a6 by decide, show Reg.a4 ≠ Reg.a6 by decide,
    show Reg.a6 ≠ Reg.a4 by decide, show Reg.a5 ≠ Reg.a6 by decide, show Reg.a6 ≠ Reg.a5 by decide,
    show Reg.a4 ≠ Reg.a7 by decide, show Reg.a7 ≠ Reg.a4 by decide, show Reg.a5 ≠ Reg.a7 by decide,
    show Reg.a7 ≠ Reg.a5 by decide, show Reg.t0 ≠ Reg.a4 by decide, show Reg.a4 ≠ Reg.t0 by decide,
    show Reg.t0 ≠ Reg.a5 by decide, show Reg.a5 ≠ Reg.t0 by decide, show Reg.t0 ≠ Reg.a6 by decide,
    show Reg.a6 ≠ Reg.t0 by decide, show Reg.t0 ≠ Reg.a7 by decide, show Reg.a7 ≠ Reg.t0 by decide]
  have hq := (s.gpr r).isLt
  have e := shl_shr (s.gpr r)
  have hsr : (s.gpr r >>> 32).toNat = (s.gpr r).toNat / 2 ^ 32 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hsl : (s.gpr r <<< 32).toNat = (s.gpr r).toNat * 2 ^ 32 % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have f1 := sub_borrow (s.gpr r) (s.gpr r <<< 32)
  have f2 := sub_borrow (s.gpr r) (s.gpr r >>> 32)
  have f3 := sub_borrow (s.gpr r - s.gpr r >>> 32) (if s.gpr r < s.gpr r <<< 32 then 1 else 0)
  have bt := sltu_toNat (s.gpr r) (s.gpr r <<< 32)
  generalize (s.gpr r <<< 32) = L at *
  generalize (s.gpr r >>> 32) = H at *
  generalize (if s.gpr r < L then (1 : BitVec 64) else 0) = B at *
  have hL := L.isLt
  have hpos : (s.gpr r).toNat / 2 ^ 32 < (s.gpr r).toNat ∨ (s.gpr r).toNat = 0 := by omega
  refine ⟨e, ?_, ?_, ?_, fun r' hr => ?_, rfl, rfl, rfl, rfl⟩
  · generalize (s.gpr r).toNat = q at *
    generalize (s.gpr r - L).toNat = lo at *
    generalize (s.gpr r - H - B).toNat = hi at *
    generalize (s.gpr r - H).toNat = d at *
    rw [hsr] at f2 e
    split at bt <;> split at f1 <;> split at f2 <;> split at f3 <;> omega
  · rw [hsr]; omega
  · generalize (s.gpr r).toNat = q at *
    generalize (s.gpr r - H - B).toNat = hi at *
    generalize (s.gpr r - H).toNat = d at *
    rw [hsr] at f2 e
    split at bt <;> split at f1 <;> split at f2 <;> split at f3 <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.Weierstrass.RISCV64.P256Field
