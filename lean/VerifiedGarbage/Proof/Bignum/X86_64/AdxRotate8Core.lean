module

public import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxRotate8
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxStep
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Bignum.X86_64.AdxRotate8Math`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxRotate8
theorem combine {a0 a1 a2 a3 a4 a5 a6 a7 p0 p1 p2 p3 p4 p5 p6 p7 h0 h1 h2 h3 h4 h5 h6 h7 l0 l1 l2 l3 l4 l5 l6 l7 l8 c0 c1 c2 c3 c4 c5 c6 c7 o0 o1 o2 o3 o4 o5 o6 ct ot : Nat}
    (e0 : l0 + 2 ^ 64 * c0 + 2 ^ 64 * h0 + 2 ^ 128 * o0 = a0 + p0 + 0 + 2 ^ 64 * a1 + 2 ^ 64 * 0)
    (e1 : l1 + 2 ^ 64 * c1 + 2 ^ 64 * h1 + 2 ^ 128 * o1 = h0 + p1 + c0 + 2 ^ 64 * a2 + 2 ^ 64 * o0)
    (e2 : l2 + 2 ^ 64 * c2 + 2 ^ 64 * h2 + 2 ^ 128 * o2 = h1 + p2 + c1 + 2 ^ 64 * a3 + 2 ^ 64 * o1)
    (e3 : l3 + 2 ^ 64 * c3 + 2 ^ 64 * h3 + 2 ^ 128 * o3 = h2 + p3 + c2 + 2 ^ 64 * a4 + 2 ^ 64 * o2)
    (e4 : l4 + 2 ^ 64 * c4 + 2 ^ 64 * h4 + 2 ^ 128 * o4 = h3 + p4 + c3 + 2 ^ 64 * a5 + 2 ^ 64 * o3)
    (e5 : l5 + 2 ^ 64 * c5 + 2 ^ 64 * h5 + 2 ^ 128 * o5 = h4 + p5 + c4 + 2 ^ 64 * a6 + 2 ^ 64 * o4)
    (e6 : l6 + 2 ^ 64 * c6 + 2 ^ 64 * h6 + 2 ^ 128 * o6 = h5 + p6 + c5 + 2 ^ 64 * a7 + 2 ^ 64 * o5)
    (e7 : l7 + 2 ^ 64 * h7 + 2 ^ 64 * c7 = h6 + p7 + c6)
    (e8 : l8 + 2 ^ 64 * ct + 2 ^ 64 * ot = h7 + c7 + o6) :
    l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3 + 2 ^ 256 * l4 + 2 ^ 320 * l5 + 2 ^ 384 * l6 + 2 ^ 448 * l7 + 2 ^ 512 * l8 + 2 ^ 576 * (ct + ot) =
      a0 + p0 + 2 ^ 64 * (a1 + p1) + 2 ^ 128 * (a2 + p2) + 2 ^ 192 * (a3 + p3) + 2 ^ 256 * (a4 + p4) + 2 ^ 320 * (a5 + p5) + 2 ^ 384 * (a6 + p6) + 2 ^ 448 * (a7 + p7) := by
  omega_using [e0, e1, e2, e3, e4, e5, e6, e7, e8]
theorem extend_blocks {P R L C X T U N O C' A B : Nat}
    (h : L + P * C = X + T + U * N) (h' : O + R * C' = C + A + U * B) :
    L + P * O + P * R * C' = X + (T + P * A) + U * (N + P * B) := by
  grind
theorem tile_combine {R P H A U N₀ L C T N₁ Y K V Q : Nat}
    (h₀ : R * H = A + U * N₀) (h₁ : L + P * C = H + T + U * N₁)
    (h₂ : Y + R * K = C + V + Q) :
    R * (L + P * Y + (P * R) * K) =
      (A + R * T + (P * R) * V) + (P * R) * Q + U * (N₀ + R * N₁) := by
  grind
theorem extend_high {R P X Y C D U N H : Nat}
    (h : R * (X + P * C) = Y + P * D + U * N) :
    R * (X + P * H + P * C) = Y + (P * R) * H + P * D + U * N := by
  grind
theorem radix_bound {q P u R : Nat} (hq : q < P) (hu : u < R) : q + P * u < P * R := by
  have h := Nat.mul_le_mul_left P (show u + 1 ≤ R by omega_using [hu])
  rw [Nat.mul_add, Nat.mul_one] at h
  omega_using [hq, h]

theorem extend_tiles {P R X Y T q u N : Nat}
    (h : P * X = T + q * N) (h' : R * Y = X + u * N) :
    (P * R) * Y = T + (q + P * u) * N := by
  grind
end VG.Proof.Bignum.X86_64.AdxRotate8

end

end

/-! ### `Bignum.X86_64.AdxRotate8Word`, which this module and modules that import it used -/

section

/-! Numeric equations for a rotating ADX column, including both live flags. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem word_ok (s : State) {k : Nat} {hi prev next : Reg} {v : BitVec 64} {c o : Bool}
    (hm : readSrc s (.mem (at_ .rbp (8 * k))) = some v)
    (hc : s.cf = some c) (ho : s.of = some o)
    (h1 : hi ≠ .rax) (h2 : prev ≠ hi) (h3 : prev ≠ .rax)
    (h4 : next ≠ hi) (h5 : next ≠ .rax) (h6 : next ≠ prev) :
    WP isa (.block (AdxRotate8.word k hi prev next)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      (t.gpr prev).toNat + 2 ^ 64 * c'.toNat + 2 ^ 64 * (t.gpr hi).toNat +
        2 ^ 128 * o'.toNat =
      (s.gpr prev).toNat + (s.gpr .rdx).toNat * v.toNat + c.toNat +
        2 ^ 64 * (s.gpr next).toNat + 2 ^ 64 * o.toNat ∧ Keeps [hi, .rax, prev] s t := by
  rw [show AdxRotate8.word k hi prev next = ([.mulx hi .rax (.mem (at_ .rbp (8 * k)))] : List Instr) ++
    (([.adcx prev (.reg .rax)] : List Instr) ++ [.adox hi (.reg next)]) from rfl, WP.block_append_iff]
  refine WP.mono (mulx_ok s hm (fun _ h => nomatch h) h1) fun a ⟨ea, ca, oa, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok a (src := .reg .rax) rfl (fun _ h => nomatch h) (ca.trans hc))
    fun b ⟨cb, hcb, hob, eb, kb⟩ => ?_
  refine WP.mono (adox_ok b (src := .reg next) rfl (fun _ h => nomatch h) (hob.trans (oa.trans ho)))
    fun t ⟨ot, hot, hct, et, kt⟩ => ?_
  refine ⟨cb, ot, hct.trans hcb, hot, ?_, (ka.trans (kb.trans kt)).mono (by simp)⟩
  have ep : a.gpr prev = s.gpr prev := ka.gpr (by simp [h2, h3])
  have en : b.gpr next = s.gpr next := (kb.gpr (by simp [h6])).trans (ka.gpr (by simp [h4, h5]))
  have eh : b.gpr hi = a.gpr hi := kb.gpr (by simp [Ne.symm h2])
  have eo : t.gpr prev = b.gpr prev := kt.gpr (by simp [h2])
  rw [ep] at eb
  rw [en, eh] at et
  rw [eo]
  omega_using [ea, eb, et]

theorem close_ok (s : State) {c o : Bool} (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block AdxRotate8.close) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      (t.gpr .r15).toNat + 2 ^ 64 * c'.toNat + 2 ^ 64 * o'.toNat =
        (s.gpr .r15).toNat + c.toNat + o.toNat ∧ Keeps [.rax, .r15] s t := by
  rw [show AdxRotate8.close = ([.mov32 .rax (.imm 0)] : List Instr) ++
    (([.adox .r15 (.reg .rax)] : List Instr) ++ [.adcx .r15 (.reg .rax)]) from rfl, WP.block_append_iff]
  refine WP.mono (movZero_ok s .rax) fun a ⟨za, ca, oa, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adox_ok a (src := .reg .rax) rfl (fun _ h => nomatch h) (oa.trans ho))
    fun b ⟨ob, hob, hcb, eb, kb⟩ => ?_
  refine WP.mono (adcx_ok b (src := .reg .rax) rfl (fun _ h => nomatch h) (hcb.trans (ca.trans hc)))
    fun t ⟨ct, hct, hot, et, kt⟩ => ?_
  refine ⟨ct, ob, hct, hot.trans hob, ?_, (ka.trans (kb.trans kt)).mono (by simp)⟩
  have ep : a.gpr .r15 = s.gpr .r15 := ka.gpr (by decide)
  have zb : b.gpr .rax = 0 := (kb.gpr (by decide)).trans za
  rw [ep, za] at eb
  rw [zb] at et
  simp only [show (0 : BitVec 64).toNat = 0 from rfl] at eb et
  omega_using [eb, et]
end VG.Proof.Bignum.X86_64.AdxRotate8

end

end

/-! Eight rotating columns compute an exact multiply-add and one-word shift. -/

@[expose] public section

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
  obtain h8 := (s.gpr .r8).isLt; have h9 := (s.gpr .r9).isLt
  obtain h10 := (s.gpr .r10).isLt; have h11 := (s.gpr .r11).isLt
  obtain h12 := (s.gpr .r12).isLt; have h13 := (s.gpr .r13).isLt
  obtain h14 := (s.gpr .r14).isLt; have h15 := (s.gpr .r15).isLt
  unfold cols; omega_arith

theorem number_lt (v : Nat → BitVec 64) : number v < 2 ^ 512 := by
  obtain h0 := (v 0).isLt; have h1 := (v 1).isLt
  obtain h2 := (v 2).isLt; have h3 := (v 3).isLt
  obtain h4 := (v 4).isLt; have h5 := (v 5).isLt
  obtain h6 := (v 6).isLt; have h7 := (v 7).isLt
  unfold number; omega_arith

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
  omega_arith

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
  obtain m0 : readSrc a0 (.mem (at_ .rbp (8 * 0))) = some (v 0) := by
    rw [k0.readMem (by decide) (by intro r h; nomatch h)]; exact hm 0 (by decide)
  refine WP.mono (word_ok a0 m0 hc0 ho0 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun a1 ⟨c1, o1, hc1, ho1, e1, q1⟩ => ?_
  obtain k1 := k0.trans q1
  rw [WP.block_append_iff]
  obtain m1 : readSrc a1 (.mem (at_ .rbp (8 * 1))) = some (v 1) := by
    rw [k1.readMem (by decide) (by intro r h; nomatch h)]; exact hm 1 (by decide)
  refine WP.mono (word_ok a1 m1 hc1 ho1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun a2 ⟨c2, o2, hc2, ho2, e2, q2⟩ => ?_
  obtain k2 := k1.trans q2
  rw [WP.block_append_iff]
  obtain m2 : readSrc a2 (.mem (at_ .rbp (8 * 2))) = some (v 2) := by
    rw [k2.readMem (by decide) (by intro r h; nomatch h)]; exact hm 2 (by decide)
  refine WP.mono (word_ok a2 m2 hc2 ho2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun a3 ⟨c3, o3, hc3, ho3, e3, q3⟩ => ?_
  obtain k3 := k2.trans q3
  rw [WP.block_append_iff]
  obtain m3 : readSrc a3 (.mem (at_ .rbp (8 * 3))) = some (v 3) := by
    rw [k3.readMem (by decide) (by intro r h; nomatch h)]; exact hm 3 (by decide)
  refine WP.mono (word_ok a3 m3 hc3 ho3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun a4 ⟨c4, o4, hc4, ho4, e4, q4⟩ => ?_
  obtain k4 := k3.trans q4
  rw [WP.block_append_iff]
  obtain m4 : readSrc a4 (.mem (at_ .rbp (8 * 4))) = some (v 4) := by
    rw [k4.readMem (by decide) (by intro r h; nomatch h)]; exact hm 4 (by decide)
  refine WP.mono (word_ok a4 m4 hc4 ho4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun a5 ⟨c5, o5, hc5, ho5, e5, q5⟩ => ?_
  obtain k5 := k4.trans q5
  rw [WP.block_append_iff]
  obtain m5 : readSrc a5 (.mem (at_ .rbp (8 * 5))) = some (v 5) := by
    rw [k5.readMem (by decide) (by intro r h; nomatch h)]; exact hm 5 (by decide)
  refine WP.mono (word_ok a5 m5 hc5 ho5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun a6 ⟨c6, o6, hc6, ho6, e6, q6⟩ => ?_
  obtain k6 := k5.trans q6
  rw [WP.block_append_iff]
  obtain m6 : readSrc a6 (.mem (at_ .rbp (8 * 6))) = some (v 6) := by
    rw [k6.readMem (by decide) (by intro r h; nomatch h)]; exact hm 6 (by decide)
  refine WP.mono (word_ok a6 m6 hc6 ho6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun a7 ⟨c7, o7, hc7, ho7, e7, q7⟩ => ?_
  obtain k7 := k6.trans q7
  rw [WP.block_append_iff]
  obtain m7 : readSrc a7 (.mem (at_ .rbp 56)) = some (v 7) := by
    rw [k7.readMem (by decide) (by intro r h; nomatch h)]; exact hm 7 (by decide)
  refine WP.mono (last_ok a7 m7 hc7 ho7) fun a8 ⟨c8, hc8, ho8, e8, q8⟩ => ?_
  obtain k8 := k7.trans q8
  refine WP.mono (close_ok a8 hc8 ho8) fun t ⟨ct, ot, hct, hot, e9, q9⟩ => ?_
  obtain kt := k8.trans q9
  rw [k0.gpr (by decide : Reg.rdx ∉ _), k0.gpr (by decide : Reg.r9 ∉ _)] at e1
  rw [k1.gpr (by decide : Reg.rdx ∉ _), k1.gpr (by decide : Reg.r10 ∉ _)] at e2
  rw [k2.gpr (by decide : Reg.rdx ∉ _), k2.gpr (by decide : Reg.r11 ∉ _)] at e3
  rw [k3.gpr (by decide : Reg.rdx ∉ _), k3.gpr (by decide : Reg.r12 ∉ _)] at e4
  rw [k4.gpr (by decide : Reg.rdx ∉ _), k4.gpr (by decide : Reg.r13 ∉ _)] at e5
  rw [k5.gpr (by decide : Reg.rdx ∉ _), k5.gpr (by decide : Reg.r14 ∉ _)] at e6
  rw [k6.gpr (by decide : Reg.rdx ∉ _), k6.gpr (by decide : Reg.r15 ∉ _)] at e7
  rw [eh] at e1
  rw [k7.gpr (by decide : Reg.rdx ∉ _)] at e8
  obtain f1 : t.gpr .rbx = a1.gpr .rbx := (((((((q2.trans q3).trans q4).trans q5).trans q6).trans q7).trans q8).trans q9).gpr (by decide)
  obtain f2 : t.gpr .r8 = a2.gpr .r8 := ((((((q3.trans q4).trans q5).trans q6).trans q7).trans q8).trans q9).gpr (by decide)
  obtain f3 : t.gpr .r9 = a3.gpr .r9 := (((((q4.trans q5).trans q6).trans q7).trans q8).trans q9).gpr (by decide)
  obtain f4 : t.gpr .r10 = a4.gpr .r10 := ((((q5.trans q6).trans q7).trans q8).trans q9).gpr (by decide)
  obtain f5 : t.gpr .r11 = a5.gpr .r11 := (((q6.trans q7).trans q8).trans q9).gpr (by decide)
  obtain f6 : t.gpr .r12 = a6.gpr .r12 := ((q7.trans q8).trans q9).gpr (by decide)
  obtain f7 : t.gpr .r13 = a7.gpr .r13 := (q8.trans q9).gpr (by decide)
  obtain f8 : t.gpr .r14 = a8.gpr .r14 := q9.gpr (by decide)
  obtain eq : (t.gpr .rbx).toNat + 2 ^ 64 * cols t + 2 ^ 576 * (ct.toNat + ot.toNat) =
      cols s + (s.gpr .rdx).toNat * number v := by
    unfold cols number
    simp only [Nat.mul_add, Nat.mul_left_comm (s.gpr .rdx).toNat]
    rw [f1, f2, f3, f4, f5, f6, f7, f8]
    obtain combined := combine e1 e2 e3 e4 e5 e6 e7 e8 e9
    omega_using [combined]
  obtain bound : cols s + (s.gpr .rdx).toNat * number v < 2 ^ 576 := by
    obtain a := cols_lt s
    obtain b := number_lt v
    obtain d := (s.gpr .rdx).isLt
    obtain m := Nat.mul_le_mul (show (s.gpr .rdx).toNat ≤ 2 ^ 64 - 1 by omega_arith)
      (show number v ≤ 2 ^ 512 - 1 by omega_arith)
    omega_arith
  obtain z : ct = false ∧ ot = false := by
    obtain z : ct.toNat + ot.toNat = 0 := by omega_using [eq, bound]
    exact ⟨Bool.toNat_eq_zero.mp (by omega_using [z]),
      Bool.toNat_eq_zero.mp (by omega_using [z])⟩
  rcases z with ⟨rfl, rfl⟩
  refine ⟨?_, hct, hot, kt.mono (by decide)⟩
  simpa only [Bool.toNat_false, Nat.zero_add, Nat.mul_zero, Nat.add_zero] using eq
end VG.Proof.Bignum.X86_64.AdxRotate8
