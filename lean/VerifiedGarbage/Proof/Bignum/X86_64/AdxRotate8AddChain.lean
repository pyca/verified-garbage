import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Core

/-! An eight-word addition with its exact final carry. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

theorem add_combine {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 t0 t1 t2 t3 t4 t5 t6 t7 c0 c1 c2 c3 c4 c5 c6 c7 c8 : Nat}
    (h0 : t0 + 2 ^ 64 * c1 = a0 + b0 + c0)
    (h1 : t1 + 2 ^ 64 * c2 = a1 + b1 + c1)
    (h2 : t2 + 2 ^ 64 * c3 = a2 + b2 + c2)
    (h3 : t3 + 2 ^ 64 * c4 = a3 + b3 + c3)
    (h4 : t4 + 2 ^ 64 * c5 = a4 + b4 + c4)
    (h5 : t5 + 2 ^ 64 * c6 = a5 + b5 + c5)
    (h6 : t6 + 2 ^ 64 * c7 = a6 + b6 + c6)
    (h7 : t7 + 2 ^ 64 * c8 = a7 + b7 + c7)
    : t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3 + 2 ^ 256 * t4 + 2 ^ 320 * t5 + 2 ^ 384 * t6 + 2 ^ 448 * t7 + 2 ^ 512 * c8 =
      a0 + b0 + 2 ^ 64 * (a1 + b1) + 2 ^ 128 * (a2 + b2) + 2 ^ 192 * (a3 + b3) + 2 ^ 256 * (a4 + b4) + 2 ^ 320 * (a5 + b5) + 2 ^ 384 * (a6 + b6) + 2 ^ 448 * (a7 + b7) + c0 := by
  omega

theorem chain_ok (s : State) (src : Nat → Src) (v : Nat → BitVec 64) {c : Bool}
    (hc : s.cf = some c)
    (hsrc : ∀ k < 8, ∀ t, Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t →
      readSrc t (src k) = some (v k)) (himm : ∀ k < 8, ∀ n, src k ≠ .imm n) :
    WP isa (.block (AdxRotate8.addChain src)) s fun t => ∃ c' : Bool,
      t.cf = some c' ∧ cols t + 2 ^ 512 * c'.toNat = cols s + number v + c.toNat ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have k0 : Keeps [] s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  change WP isa (.block (
    ([.adcx .r8 (src 0)] : List Instr) ++ ([.adcx .r9 (src 1)] : List Instr) ++ ([.adcx .r10 (src 2)] : List Instr) ++ ([.adcx .r11 (src 3)] : List Instr) ++ ([.adcx .r12 (src 4)] : List Instr) ++ ([.adcx .r13 (src 5)] : List Instr) ++ ([.adcx .r14 (src 6)] : List Instr) ++ ([.adcx .r15 (src 7)] : List Instr))) s _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok s (hsrc 0 (by decide) s (k0.mono (by simp)))
    (himm 0 (by decide)) hc) fun a1 ⟨c1, hc1, _, e1, q1⟩ => ?_
  have k1 := k0.trans q1
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok a1 (hsrc 1 (by decide) a1 (k1.mono (by simp)))
    (himm 1 (by decide)) hc1) fun a2 ⟨c2, hc2, _, e2, q2⟩ => ?_
  have k2 := k1.trans q2
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok a2 (hsrc 2 (by decide) a2 (k2.mono (by simp)))
    (himm 2 (by decide)) hc2) fun a3 ⟨c3, hc3, _, e3, q3⟩ => ?_
  have k3 := k2.trans q3
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok a3 (hsrc 3 (by decide) a3 (k3.mono (by simp)))
    (himm 3 (by decide)) hc3) fun a4 ⟨c4, hc4, _, e4, q4⟩ => ?_
  have k4 := k3.trans q4
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok a4 (hsrc 4 (by decide) a4 (k4.mono (by simp)))
    (himm 4 (by decide)) hc4) fun a5 ⟨c5, hc5, _, e5, q5⟩ => ?_
  have k5 := k4.trans q5
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok a5 (hsrc 5 (by decide) a5 (k5.mono (by simp)))
    (himm 5 (by decide)) hc5) fun a6 ⟨c6, hc6, _, e6, q6⟩ => ?_
  have k6 := k5.trans q6
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok a6 (hsrc 6 (by decide) a6 (k6.mono (by simp)))
    (himm 6 (by decide)) hc6) fun a7 ⟨c7, hc7, _, e7, q7⟩ => ?_
  have k7 := k6.trans q7
  refine WP.mono (adcx_ok a7 (hsrc 7 (by decide) a7 (k7.mono (by simp)))
    (himm 7 (by decide)) hc7) fun a8 ⟨c8, hc8, _, e8, q8⟩ => ?_
  have k8 := k7.trans q8
  rw [k1.gpr (by decide : Reg.r9 ∉ _)] at e2
  rw [k2.gpr (by decide : Reg.r10 ∉ _)] at e3
  rw [k3.gpr (by decide : Reg.r11 ∉ _)] at e4
  rw [k4.gpr (by decide : Reg.r12 ∉ _)] at e5
  rw [k5.gpr (by decide : Reg.r13 ∉ _)] at e6
  rw [k6.gpr (by decide : Reg.r14 ∉ _)] at e7
  rw [k7.gpr (by decide : Reg.r15 ∉ _)] at e8
  have f1 : a8.gpr .r8 = a1.gpr .r8 := ((((((q2.trans q3).trans q4).trans q5).trans q6).trans q7).trans q8).gpr (by decide)
  have f2 : a8.gpr .r9 = a2.gpr .r9 := (((((q3.trans q4).trans q5).trans q6).trans q7).trans q8).gpr (by decide)
  have f3 : a8.gpr .r10 = a3.gpr .r10 := ((((q4.trans q5).trans q6).trans q7).trans q8).gpr (by decide)
  have f4 : a8.gpr .r11 = a4.gpr .r11 := (((q5.trans q6).trans q7).trans q8).gpr (by decide)
  have f5 : a8.gpr .r12 = a5.gpr .r12 := ((q6.trans q7).trans q8).gpr (by decide)
  have f6 : a8.gpr .r13 = a6.gpr .r13 := (q7.trans q8).gpr (by decide)
  have f7 : a8.gpr .r14 = a7.gpr .r14 := q8.gpr (by decide)
  refine ⟨c8, hc8, ?_, k8.mono (by simp)⟩
  unfold cols number
  rw [f1, f2, f3, f4, f5, f6, f7]
  have h := add_combine e1 e2 e3 e4 e5 e6 e7 e8
  omega_using [h]
end VG.Proof.Bignum.X86_64.AdxRotate8
