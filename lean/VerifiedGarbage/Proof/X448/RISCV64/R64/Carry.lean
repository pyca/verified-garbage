module

import VerifiedGarbage.Proof.X448.RISCV64.R64.Macc
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.X448.RISCV64.R64
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic

/-!
# X448 on RISC-V, 64-bit limbs: carries and borrows

`add r r v; sltu o r v` is `r + v` in two words (`addOut_ok`), `sltu o r v;
sub r r v` is `r - v` with the borrow (`subOut_ok`); `foldR c` adds
`c (1 + 2²²⁴)` to the seven words in `w 0`–`w 6` (`foldR_ok`) and
`unfoldR c` subtracts it (`unfoldR_ok`), each with the carry (borrow) out in
`c`.
-/

-- separate module: its proofs (about 6.5 s) cost more than its imports, and `Reduce`'s
-- changes need not re-check them

@[expose] public section

namespace VG.Proof.X448.RISCV64.R64

open VG VG.RISCV64 VG.RISCV64.Wide VG.Impl.X448.RISCV64.R64
open VG.Proof.X25519.RISCV64 (WP.append)

variable {s : State}

set_option linter.unusedSimpArgs false in
/-- `r + v`, its carry into `o` (which may be `v`). -/
theorem addOut_ok {r v o : Reg} (hrv : r ≠ v) (hro : r ≠ o) :
    WP isa (.block [.add r r v, .sltu o r v]) s fun s' =>
      (s'.gpr r).toNat + 2 ^ 64 * (s'.gpr o).toNat = (s.gpr r).toNat + (s.gpr v).toNat ∧
      Keeps [r, o] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu,
    RegUpd.gpr_write, hrv, hro, Ne.symm hrv, Ne.symm hro, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨Wide.carry _ _, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  simp only [RegUpd.gpr_write, hx.1, hx.2, ite_false]

/-- The borrow out of `a - b`, as `sltu` computes it before the subtraction. -/
theorem borrow (a b : BitVec 64) :
    (a - b).toNat + b.toNat = a.toNat + 2 ^ 64 * (if a < b then (1 : BitVec 64) else 0).toNat := by
  have ha := a.isLt; have hb := b.isLt
  rw [BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat
  · have hlt : a < b := BitVec.lt_def.mpr h
    simp only [hlt, ↓reduceIte]
    show _ = _ + 2 ^ 64 * 1
    omega
  · have hlt : ¬ a < b := fun h' => h (BitVec.lt_def.mp h')
    simp only [hlt, ↓reduceIte]
    show _ = _ + 2 ^ 64 * 0
    omega

set_option linter.unusedSimpArgs false in
/-- `r - v`, its borrow into `o`. -/
theorem subOut_ok {r v o : Reg} (hro : r ≠ o) (hov : o ≠ v) :
    WP isa (.block [.sltu o r v, .sub r r v]) s fun s' =>
      (s'.gpr r).toNat + (s.gpr v).toNat = (s.gpr r).toNat + 2 ^ 64 * (s'.gpr o).toNat ∧
      Keeps [r, o] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_sub, exec_sltu,
    RegUpd.gpr_write, hro, hov, Ne.symm hro, Ne.symm hov, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨borrow _ _, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  simp only [RegUpd.gpr_write, hx.1, hx.2, ite_false]

set_option linter.unusedSimpArgs false in
/-- `d := a + b` without wrapping. -/
theorem addSmall_ok {d a b : Reg} :
    WP isa (.block [.add d a b]) s fun s' =>
      ((s.gpr a).toNat + (s.gpr b).toNat < 2 ^ 64 →
        (s'.gpr d).toNat = (s.gpr a).toNat + (s.gpr b).toNat) ∧ Keeps [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, RegUpd.gpr_write, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun h => by rw [BitVec.toNat_add, Nat.mod_eq_of_lt h], fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [RegUpd.gpr_write, hx, ite_false]

set_option linter.unusedSimpArgs false in
/-- `d := a << 32` of a small `a`. -/
theorem shl32_ok {d a : Reg} :
    WP isa (.block [.shift .sll .d d a 32]) s fun s' =>
      ((s.gpr a).toNat < 2 ^ 32 → (s'.gpr d).toNat = 2 ^ 32 * (s.gpr a).toNat) ∧ Keeps [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_shift_d (show 32 < 64 by decide),
    RegUpd.gpr_write, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨fun h => by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega, fun x hx => ?_, rfl, rfl,
    rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [RegUpd.gpr_write, hx, ite_false]

/-- An update keeps all but its register. -/
theorem Keeps.rest_mono_of_upd {s s' : State} {d : Reg} {v : BitVec 64} (u : Steps.Upd s s' d v) :
    Keeps [d] s s' :=
  ⟨fun r hr => u.other r (by simpa using hr), u.mem, u.rd, u.wr, u.sp⟩

/-- The seven words in `w 0`–`w 6`. -/
abbrev rw7 (s : State) : Nat := val7 fun i => (s.gpr (w i)).toNat

theorem foldR_eq : foldR .a5 =
    ([.add (w 0) (w 0) .a5, .sltu .t0 (w 0) .a5] : List Instr) ++
    (([.add (w 1) (w 1) .t0, .sltu .t0 (w 1) .t0] : List Instr) ++
    (([.add (w 2) (w 2) .t0, .sltu .t0 (w 2) .t0] : List Instr) ++
    (([.add (w 3) (w 3) .t0, .sltu .t0 (w 3) .t0] : List Instr) ++
    (([.shift .sll .d .a7 .a5 32] : List Instr) ++
    (([.add (w 3) (w 3) .a7, .sltu .a7 (w 3) .a7] : List Instr) ++
    (([.add .t0 .t0 .a7] : List Instr) ++
    (([.add (w 4) (w 4) .t0, .sltu .t0 (w 4) .t0] : List Instr) ++
    (([.add (w 5) (w 5) .t0, .sltu .t0 (w 5) .t0] : List Instr) ++
    (([.add (w 6) (w 6) .t0, .sltu .a5 (w 6) .t0] : List Instr)))))))))) := rfl

/-- `foldR a5`: the seven words plus `c (1 + 2²²⁴)`, for `c < 2³²` in `a5`,
the carry out in `a5`. -/
theorem foldR_ok :
    WP isa (.block (foldR .a5)) s fun s' =>
      ((s.gpr .a5).toNat < 2 ^ 32 →
        rw7 s' + (2 ^ 64) ^ 7 * (s'.gpr .a5).toNat =
          rw7 s + (s.gpr .a5).toNat + 2 ^ 224 * (s.gpr .a5).toNat) ∧
      Keeps [.t3, .t4, .t5, .t6, .a1, .a2, .a4, .a5, .a7, .t0] s s' := by
  rw [foldR_eq]
  refine WP.append (addOut_ok (by decide) (by decide)) fun s1 ⟨e1, k1⟩ => ?_
  refine WP.append (addOut_ok (by decide) (by decide)) fun s2 ⟨e2, k2⟩ => ?_
  refine WP.append (addOut_ok (by decide) (by decide)) fun s3 ⟨e3, k3⟩ => ?_
  refine WP.append (addOut_ok (by decide) (by decide)) fun s4 ⟨e4, k4⟩ => ?_
  refine WP.append shl32_ok fun s5 ⟨e5, k5⟩ => ?_
  refine WP.append (addOut_ok (by decide) (by decide)) fun s6 ⟨e6, k6⟩ => ?_
  refine WP.append addSmall_ok fun s7 ⟨e7, k7⟩ => ?_
  refine WP.append (addOut_ok (by decide) (by decide)) fun s8 ⟨e8, k8⟩ => ?_
  refine WP.append (addOut_ok (by decide) (by decide)) fun s9 ⟨e9, k9⟩ => ?_
  refine WP.mono (addOut_ok (by decide) (by decide)) fun s10 ⟨e10, k10⟩ => ⟨fun hc => ?_, ?_⟩
  · have k := ((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans k8).trans
      k9).trans k10
    -- the registers each step reads, through the later steps
    have c5 : s4.gpr .a5 = s.gpr .a5 := by
      rw [k4.1 _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide)]
    rw [c5] at e5
    have e5 := e5 hc
    have l1 : s10.gpr (w 0) = s1.gpr (w 0) := by
      rw [k10.1 _ (by decide), k9.1 _ (by decide), k8.1 _ (by decide), k7.1 _ (by decide),
        k6.1 _ (by decide), k5.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide),
        k2.1 _ (by decide)]
    have l2 : s10.gpr (w 1) = s2.gpr (w 1) := by
      rw [k10.1 _ (by decide), k9.1 _ (by decide), k8.1 _ (by decide), k7.1 _ (by decide),
        k6.1 _ (by decide), k5.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide)]
    have l3 : s10.gpr (w 2) = s3.gpr (w 2) := by
      rw [k10.1 _ (by decide), k9.1 _ (by decide), k8.1 _ (by decide), k7.1 _ (by decide),
        k6.1 _ (by decide), k5.1 _ (by decide), k4.1 _ (by decide)]
    have l4 : s10.gpr (w 3) = s6.gpr (w 3) := by
      rw [k10.1 _ (by decide), k9.1 _ (by decide), k8.1 _ (by decide), k7.1 _ (by decide)]
    have l5 : s10.gpr (w 4) = s8.gpr (w 4) := by rw [k10.1 _ (by decide), k9.1 _ (by decide)]
    have l6 : s10.gpr (w 5) = s9.gpr (w 5) := by rw [k10.1 _ (by decide)]
    have r0 : s.gpr (w 0) = s.gpr (w 0) := rfl
    have r1 : s1.gpr (w 1) = s.gpr (w 1) := k1.1 _ (by decide)
    have r2 : s2.gpr (w 2) = s.gpr (w 2) := by rw [k2.1 _ (by decide), k1.1 _ (by decide)]
    have r3 : s3.gpr (w 3) = s.gpr (w 3) := by
      rw [k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide)]
    have r4 : s7.gpr (w 4) = s.gpr (w 4) := by
      rw [k7.1 _ (by decide), k6.1 _ (by decide), k5.1 _ (by decide), k4.1 _ (by decide),
        k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide)]
    have r5 : s8.gpr (w 5) = s.gpr (w 5) := by
      rw [k8.1 _ (by decide), k7.1 _ (by decide), k6.1 _ (by decide), k5.1 _ (by decide),
        k4.1 _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide)]
    have r6 : s9.gpr (w 6) = s.gpr (w 6) := by
      rw [k9.1 _ (by decide), k8.1 _ (by decide), k7.1 _ (by decide), k6.1 _ (by decide),
        k5.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide),
        k1.1 _ (by decide)]
    have t4 : s5.gpr (w 3) = s4.gpr (w 3) := k5.1 _ (by decide)
    have t5 : s5.gpr .t0 = s4.gpr .t0 := k5.1 _ (by decide)
    have t6 : s6.gpr .t0 = s5.gpr .t0 := k6.1 _ (by decide)
    rw [r1] at e2; rw [r2] at e3; rw [r3] at e4; rw [t4] at e6
    rw [r4] at e8; rw [r5] at e9; rw [r6] at e10
    have t7 : s6.gpr .t0 = s4.gpr .t0 := by rw [t6, t5]
    rw [t7] at e7
    have hb : ∀ (x : State) (r : Reg), (x.gpr r).toNat < 2 ^ 64 := fun x r => (x.gpr r).isLt
    have := hb s1 .t0; have := hb s2 .t0; have := hb s3 .t0; have := hb s4 .t0; have := hb s6 .a7
    have := hb s1 (w 0); have := hb s2 (w 1); have := hb s3 (w 2); have := hb s4 (w 3)
    have := hb s6 (w 3); have := hb s8 (w 4); have := hb s9 (w 5); have := hb s10 (w 6)
    have := hb s7 .t0; have := hb s8 .t0; have := hb s9 .t0; have := hb s10 .a5
    have := hb s (w 0); have := hb s (w 1); have := hb s (w 2); have := hb s (w 3)
    have := hb s (w 4); have := hb s (w 5); have := hb s (w 6)
    have e7 := e7 (by omega)
    simp only [rw7, val7, l1, l2, l3, l4, l5, l6]
    omega
  · exact (((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans k8).trans
      k9).trans k10).mono (by decide)

theorem unfoldR_eq : unfoldR .a5 =
    ([.sltu .t0 (w 0) .a5, .sub (w 0) (w 0) .a5] : List Instr) ++
    (([.sltu .a7 (w 1) .t0, .sub (w 1) (w 1) .t0] : List Instr) ++
    (([.sltu .t0 (w 2) .a7, .sub (w 2) (w 2) .a7] : List Instr) ++
    (([.sltu .a7 (w 3) .t0, .sub (w 3) (w 3) .t0] : List Instr) ++
    (([.shift .sll .d .t0 .a5 32] : List Instr) ++
    (([.sltu .a5 (w 3) .t0, .sub (w 3) (w 3) .t0] : List Instr) ++
    (([.add .a7 .a7 .a5] : List Instr) ++
    (([.sltu .t0 (w 4) .a7, .sub (w 4) (w 4) .a7] : List Instr) ++
    (([.sltu .a7 (w 5) .t0, .sub (w 5) (w 5) .t0] : List Instr) ++
    (([.sltu .a5 (w 6) .a7, .sub (w 6) (w 6) .a7] : List Instr)))))))))) := rfl

/-- `unfoldR a5`: the seven words less `c (1 + 2²²⁴)`, for `c < 2³²` in `a5`,
the borrow out in `a5`. -/
theorem unfoldR_ok :
    WP isa (.block (unfoldR .a5)) s fun s' =>
      ((s.gpr .a5).toNat < 2 ^ 32 →
        rw7 s' + (s.gpr .a5).toNat + 2 ^ 224 * (s.gpr .a5).toNat =
          rw7 s + (2 ^ 64) ^ 7 * (s'.gpr .a5).toNat) ∧
      Keeps [.t3, .t4, .t5, .t6, .a1, .a2, .a4, .a5, .a7, .t0] s s' := by
  rw [unfoldR_eq]
  refine WP.append (subOut_ok (by decide) (by decide)) fun s1 ⟨e1, k1⟩ => ?_
  refine WP.append (subOut_ok (by decide) (by decide)) fun s2 ⟨e2, k2⟩ => ?_
  refine WP.append (subOut_ok (by decide) (by decide)) fun s3 ⟨e3, k3⟩ => ?_
  refine WP.append (subOut_ok (by decide) (by decide)) fun s4 ⟨e4, k4⟩ => ?_
  refine WP.append shl32_ok fun s5 ⟨e5, k5⟩ => ?_
  refine WP.append (subOut_ok (by decide) (by decide)) fun s6 ⟨e6, k6⟩ => ?_
  refine WP.append addSmall_ok fun s7 ⟨e7, k7⟩ => ?_
  refine WP.append (subOut_ok (by decide) (by decide)) fun s8 ⟨e8, k8⟩ => ?_
  refine WP.append (subOut_ok (by decide) (by decide)) fun s9 ⟨e9, k9⟩ => ?_
  refine WP.mono (subOut_ok (by decide) (by decide)) fun s10 ⟨e10, k10⟩ => ⟨fun hc => ?_, ?_⟩
  · have c5 : s4.gpr .a5 = s.gpr .a5 := by
      rw [k4.1 _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide)]
    rw [c5] at e5
    have e5 := e5 hc
    have l1 : s10.gpr (w 0) = s1.gpr (w 0) := by
      rw [k10.1 _ (by decide), k9.1 _ (by decide), k8.1 _ (by decide), k7.1 _ (by decide),
        k6.1 _ (by decide), k5.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide),
        k2.1 _ (by decide)]
    have l2 : s10.gpr (w 1) = s2.gpr (w 1) := by
      rw [k10.1 _ (by decide), k9.1 _ (by decide), k8.1 _ (by decide), k7.1 _ (by decide),
        k6.1 _ (by decide), k5.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide)]
    have l3 : s10.gpr (w 2) = s3.gpr (w 2) := by
      rw [k10.1 _ (by decide), k9.1 _ (by decide), k8.1 _ (by decide), k7.1 _ (by decide),
        k6.1 _ (by decide), k5.1 _ (by decide), k4.1 _ (by decide)]
    have l4 : s10.gpr (w 3) = s6.gpr (w 3) := by
      rw [k10.1 _ (by decide), k9.1 _ (by decide), k8.1 _ (by decide), k7.1 _ (by decide)]
    have l5 : s10.gpr (w 4) = s8.gpr (w 4) := by rw [k10.1 _ (by decide), k9.1 _ (by decide)]
    have l6 : s10.gpr (w 5) = s9.gpr (w 5) := by rw [k10.1 _ (by decide)]
    have r1 : s1.gpr (w 1) = s.gpr (w 1) := k1.1 _ (by decide)
    have r2 : s2.gpr (w 2) = s.gpr (w 2) := by rw [k2.1 _ (by decide), k1.1 _ (by decide)]
    have r3 : s3.gpr (w 3) = s.gpr (w 3) := by
      rw [k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide)]
    have r4 : s7.gpr (w 4) = s.gpr (w 4) := by
      rw [k7.1 _ (by decide), k6.1 _ (by decide), k5.1 _ (by decide), k4.1 _ (by decide),
        k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide)]
    have r5 : s8.gpr (w 5) = s.gpr (w 5) := by
      rw [k8.1 _ (by decide), k7.1 _ (by decide), k6.1 _ (by decide), k5.1 _ (by decide),
        k4.1 _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide)]
    have r6 : s9.gpr (w 6) = s.gpr (w 6) := by
      rw [k9.1 _ (by decide), k8.1 _ (by decide), k7.1 _ (by decide), k6.1 _ (by decide),
        k5.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide),
        k1.1 _ (by decide)]
    have t4 : s5.gpr (w 3) = s4.gpr (w 3) := k5.1 _ (by decide)
    have t6 : s6.gpr .a7 = s4.gpr .a7 := by rw [k6.1 _ (by decide), k5.1 _ (by decide)]
    rw [r1] at e2; rw [r2] at e3; rw [r3] at e4; rw [t4] at e6
    rw [r4] at e8; rw [r5] at e9; rw [r6] at e10; rw [t6] at e7
    have hb : ∀ (x : State) (r : Reg), (x.gpr r).toNat < 2 ^ 64 := fun x r => (x.gpr r).isLt
    have := hb s1 .t0; have := hb s2 .a7; have := hb s3 .t0; have := hb s4 .a7; have := hb s6 .a5
    have := hb s1 (w 0); have := hb s2 (w 1); have := hb s3 (w 2); have := hb s4 (w 3)
    have := hb s6 (w 3); have := hb s8 (w 4); have := hb s9 (w 5); have := hb s10 (w 6)
    have := hb s7 .a7; have := hb s8 .t0; have := hb s9 .a7; have := hb s10 .a5; have := hb s5 .t0
    have := hb s (w 0); have := hb s (w 1); have := hb s (w 2); have := hb s (w 3)
    have := hb s (w 4); have := hb s (w 5); have := hb s (w 6)
    have e7 := e7 (by omega)
    simp only [rw7, val7, l1, l2, l3, l4, l5, l6]
    omega
  · exact (((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans k8).trans
      k9).trans k10).mono (by decide)

end VG.Proof.X448.RISCV64.R64
