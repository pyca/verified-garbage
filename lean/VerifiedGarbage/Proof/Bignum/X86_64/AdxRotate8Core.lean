import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Word
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Math
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalStep

/-! Eight rotating columns compute an exact multiply-add and one-word shift. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)
open VG.Proof.MlKem.X86_64 (WP.keep)

def cols (s : State) : Nat :=
  (s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r9).toNat + 2 ^ 128 * (s.gpr .r10).toNat +
  2 ^ 192 * (s.gpr .r11).toNat + 2 ^ 256 * (s.gpr .r12).toNat +
  2 ^ 320 * (s.gpr .r13).toNat + 2 ^ 384 * (s.gpr .r14).toNat + 2 ^ 448 * (s.gpr .r15).toNat

def number (v : Nat → BitVec 64) : Nat :=
  (v 0).toNat + 2 ^ 64 * (v 1).toNat + 2 ^ 128 * (v 2).toNat +
  2 ^ 192 * (v 3).toNat + 2 ^ 256 * (v 4).toNat +
  2 ^ 320 * (v 5).toNat + 2 ^ 384 * (v 6).toNat + 2 ^ 448 * (v 7).toNat

theorem cols_lt (s : State) : cols s < 2 ^ 512 := by
  have h8 := (s.gpr .r8).isLt; have h9 := (s.gpr .r9).isLt
  have h10 := (s.gpr .r10).isLt; have h11 := (s.gpr .r11).isLt
  have h12 := (s.gpr .r12).isLt; have h13 := (s.gpr .r13).isLt
  have h14 := (s.gpr .r14).isLt; have h15 := (s.gpr .r15).isLt
  unfold cols; omega

theorem number_lt (v : Nat → BitVec 64) : number v < 2 ^ 512 := by
  have h0 := (v 0).isLt; have h1 := (v 1).isLt
  have h2 := (v 2).isLt; have h3 := (v 3).isLt
  have h4 := (v 4).isLt; have h5 := (v 5).isLt
  have h6 := (v 6).isLt; have h7 := (v 7).isLt
  unfold number; omega

theorem head_ok (s : State) :
    WP isa (.block [.mov .rbx (.reg .r8), .alu32 .xor .rax (.reg .rax)]) s fun t =>
      t.gpr .rbx = s.gpr .r8 ∧ t.cf = some false ∧ t.of = some false ∧ Keeps [.rbx, .rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    execAlu32, readSrc32, Option.bind_some, State.setReg32, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, rfl, ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_of_ne _ _ (by decide : Reg.rbx ≠ .rax),
      RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_self]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2,
      RegUpd.gpr_arithFlags]

theorem last_ok (s : State) {v : BitVec 64} {c o : Bool}
    (hm : readSrc s (.mem (at_ .rbp 56)) = some v) (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block [.mulx .r15 .rax (.mem (at_ .rbp 56)), .adcx .r14 (.reg .rax)]) s fun t =>
      ∃ c' : Bool, t.cf = some c' ∧ t.of = some o ∧
      (t.gpr .r14).toNat + 2 ^ 64 * (t.gpr .r15).toNat + 2 ^ 64 * c'.toNat =
        (s.gpr .r14).toNat + (s.gpr .rdx).toNat * v.toNat + c.toNat ∧
      Keeps [.r15, .rax, .r14] s t := by
  rw [show ([.mulx .r15 .rax (.mem (at_ .rbp 56)), .adcx .r14 (.reg .rax)] : List Instr) =
    [.mulx .r15 .rax (.mem (at_ .rbp 56))] ++ [.adcx .r14 (.reg .rax)] from rfl, WP.block_append_iff]
  refine WP.mono (mulx_ok s hm (fun _ h => nomatch h) (by decide)) fun a ⟨ea, ca, oa, ka⟩ => ?_
  refine WP.mono (adcx_ok a (src := .reg .rax) rfl (fun _ h => nomatch h) (ca.trans hc))
    fun t ⟨ct, hct, hot, et, kt⟩ => ?_
  refine ⟨ct, hct, hot.trans (oa.trans ho), ?_, (ka.trans kt).mono (by decide)⟩
  rw [ka.gpr (by decide)] at et
  rw [kt.gpr (r := .r15) (by decide)]
  omega

theorem core_ok (s : State) (v : Nat → BitVec 64)
    (hm : ∀ k < 8, readSrc s (.mem (at_ .rbp (8 * k))) = some (v k)) :
    WP isa (.block AdxRotate8.core) s fun t =>
      (t.gpr .rbx).toNat + 2 ^ 64 * cols t = cols s + (s.gpr .rdx).toNat * number v ∧
      t.cf = some false ∧ t.of = some false ∧
      Keeps [.rbx, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  unfold AdxRotate8.core
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (head_ok s) fun a0 ⟨eh, hc0, ho0, k0⟩ => ?_
  rw [WP.block_append_iff]
  have m0 : readSrc a0 (.mem (at_ .rbp (8 * 0))) = some (v 0) := by
    rw [k0.readMem (by decide) (by intro r h; nomatch h)]; exact hm 0 (by decide)
  refine WP.mono (word_ok a0 m0 hc0 ho0 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun a1 ⟨c1, o1, hc1, ho1, e1, q1⟩ => ?_
  have k1 := k0.trans q1
  rw [WP.block_append_iff]
  have m1 : readSrc a1 (.mem (at_ .rbp (8 * 1))) = some (v 1) := by
    rw [k1.readMem (by decide) (by intro r h; nomatch h)]; exact hm 1 (by decide)
  refine WP.mono (word_ok a1 m1 hc1 ho1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun a2 ⟨c2, o2, hc2, ho2, e2, q2⟩ => ?_
  have k2 := k1.trans q2
  rw [WP.block_append_iff]
  have m2 : readSrc a2 (.mem (at_ .rbp (8 * 2))) = some (v 2) := by
    rw [k2.readMem (by decide) (by intro r h; nomatch h)]; exact hm 2 (by decide)
  refine WP.mono (word_ok a2 m2 hc2 ho2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun a3 ⟨c3, o3, hc3, ho3, e3, q3⟩ => ?_
  have k3 := k2.trans q3
  rw [WP.block_append_iff]
  have m3 : readSrc a3 (.mem (at_ .rbp (8 * 3))) = some (v 3) := by
    rw [k3.readMem (by decide) (by intro r h; nomatch h)]; exact hm 3 (by decide)
  refine WP.mono (word_ok a3 m3 hc3 ho3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun a4 ⟨c4, o4, hc4, ho4, e4, q4⟩ => ?_
  have k4 := k3.trans q4
  rw [WP.block_append_iff]
  have m4 : readSrc a4 (.mem (at_ .rbp (8 * 4))) = some (v 4) := by
    rw [k4.readMem (by decide) (by intro r h; nomatch h)]; exact hm 4 (by decide)
  refine WP.mono (word_ok a4 m4 hc4 ho4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun a5 ⟨c5, o5, hc5, ho5, e5, q5⟩ => ?_
  have k5 := k4.trans q5
  rw [WP.block_append_iff]
  have m5 : readSrc a5 (.mem (at_ .rbp (8 * 5))) = some (v 5) := by
    rw [k5.readMem (by decide) (by intro r h; nomatch h)]; exact hm 5 (by decide)
  refine WP.mono (word_ok a5 m5 hc5 ho5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun a6 ⟨c6, o6, hc6, ho6, e6, q6⟩ => ?_
  have k6 := k5.trans q6
  rw [WP.block_append_iff]
  have m6 : readSrc a6 (.mem (at_ .rbp (8 * 6))) = some (v 6) := by
    rw [k6.readMem (by decide) (by intro r h; nomatch h)]; exact hm 6 (by decide)
  refine WP.mono (word_ok a6 m6 hc6 ho6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun a7 ⟨c7, o7, hc7, ho7, e7, q7⟩ => ?_
  have k7 := k6.trans q7
  rw [WP.block_append_iff]
  have m7 : readSrc a7 (.mem (at_ .rbp 56)) = some (v 7) := by
    rw [k7.readMem (by decide) (by intro r h; nomatch h)]; exact hm 7 (by decide)
  refine WP.mono (last_ok a7 m7 hc7 ho7) fun a8 ⟨c8, hc8, ho8, e8, q8⟩ => ?_
  have k8 := k7.trans q8
  refine WP.mono (close_ok a8 hc8 ho8) fun t ⟨ct, ot, hct, hot, e9, q9⟩ => ?_
  have kt := k8.trans q9
  rw [k0.gpr (by decide : Reg.rdx ∉ _), k0.gpr (by decide : Reg.r9 ∉ _)] at e1
  rw [k1.gpr (by decide : Reg.rdx ∉ _), k1.gpr (by decide : Reg.r10 ∉ _)] at e2
  rw [k2.gpr (by decide : Reg.rdx ∉ _), k2.gpr (by decide : Reg.r11 ∉ _)] at e3
  rw [k3.gpr (by decide : Reg.rdx ∉ _), k3.gpr (by decide : Reg.r12 ∉ _)] at e4
  rw [k4.gpr (by decide : Reg.rdx ∉ _), k4.gpr (by decide : Reg.r13 ∉ _)] at e5
  rw [k5.gpr (by decide : Reg.rdx ∉ _), k5.gpr (by decide : Reg.r14 ∉ _)] at e6
  rw [k6.gpr (by decide : Reg.rdx ∉ _), k6.gpr (by decide : Reg.r15 ∉ _)] at e7
  rw [eh] at e1
  rw [k7.gpr (by decide : Reg.rdx ∉ _)] at e8
  have f1 : t.gpr .rbx = a1.gpr .rbx := (((((((q2.trans q3).trans q4).trans q5).trans q6).trans q7).trans q8).trans q9).gpr (by decide)
  have f2 : t.gpr .r8 = a2.gpr .r8 := ((((((q3.trans q4).trans q5).trans q6).trans q7).trans q8).trans q9).gpr (by decide)
  have f3 : t.gpr .r9 = a3.gpr .r9 := (((((q4.trans q5).trans q6).trans q7).trans q8).trans q9).gpr (by decide)
  have f4 : t.gpr .r10 = a4.gpr .r10 := ((((q5.trans q6).trans q7).trans q8).trans q9).gpr (by decide)
  have f5 : t.gpr .r11 = a5.gpr .r11 := (((q6.trans q7).trans q8).trans q9).gpr (by decide)
  have f6 : t.gpr .r12 = a6.gpr .r12 := ((q7.trans q8).trans q9).gpr (by decide)
  have f7 : t.gpr .r13 = a7.gpr .r13 := (q8.trans q9).gpr (by decide)
  have f8 : t.gpr .r14 = a8.gpr .r14 := q9.gpr (by decide)
  have eq : (t.gpr .rbx).toNat + 2 ^ 64 * cols t + 2 ^ 576 * (ct.toNat + ot.toNat) =
      cols s + (s.gpr .rdx).toNat * number v := by
    unfold cols number
    simp only [Nat.mul_add, Nat.mul_left_comm (s.gpr .rdx).toNat]
    rw [f1, f2, f3, f4, f5, f6, f7, f8]
    have combined := combine e1 e2 e3 e4 e5 e6 e7 e8 e9
    omega_using [combined]
  have bound : cols s + (s.gpr .rdx).toNat * number v < 2 ^ 576 := by
    have a := cols_lt s
    have b := number_lt v
    have d := (s.gpr .rdx).isLt
    have m := Nat.mul_le_mul (show (s.gpr .rdx).toNat ≤ 2 ^ 64 - 1 by omega)
      (show number v ≤ 2 ^ 512 - 1 by omega)
    omega
  have z : ct = false ∧ ot = false := by
    have z : ct.toNat + ot.toNat = 0 := by omega_using [eq, bound]
    exact ⟨Bool.toNat_eq_zero.mp (by omega_using [z]),
      Bool.toNat_eq_zero.mp (by omega_using [z])⟩
  rcases z with ⟨rfl, rfl⟩
  refine ⟨?_, hct, hot, kt.mono (by decide)⟩
  simpa only [Bool.toNat_false, Nat.zero_add, Nat.mul_zero, Nat.add_zero] using eq
end VG.Proof.Bignum.X86_64.AdxRotate8
