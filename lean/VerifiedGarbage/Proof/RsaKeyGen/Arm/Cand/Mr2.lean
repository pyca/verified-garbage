module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mr1
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint7
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mont7
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Instr
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St
import VerifiedGarbage.Proof.Rsa.RecoverSubtract

/-! # A candidate on ARMv7: Miller–Rabin's start (`mrInit_vp`)

`i := 1`, `uniform := 0` and the checks `checksW w` (`checksC`, from the
comparisons of `W`): the stage before the first witness.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.Rsa.Arm.Recover (VP sub32)
open VG.Proof.RsaKeyGen (MrAt mrS wit goS shapeOf itersOf)
open VG.Proof.Rsa (b2n)

section
variable {P : CP}

theorem MS.of_upd {σ s t : State} (m : MS P σ s) {r : Reg} {v : BitVec 32} (u : Upd s t r v) : MS P σ t :=
  ⟨m.toMSp.of_same u.mem u.sp u.rd u.wr, by rw [u.mem]; exact m.stride⟩

theorem MS.of_rest {σ s t : State} (m : MS P σ s) {rs : List Reg} (r : Rest rs s t) (mem : t.mem = s.mem) :
    MS P σ t :=
  ⟨m.toMSp.of_same mem r.sp r.rd r.wr, by rw [mem]; exact m.stride⟩

theorem mrInit_vp {E : State → Prop} (hE : ∀ σ, E σ → In P σ ∧ EM P σ) :
    VP (SM P E) (.block mrInit) (MRI P E (Nt P + 1)) :=
  VP.kv mrInit_taint (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, m⟩ => by
    have pre := h.pre
    obtain ⟨fs, fw, fl, fc⟩ := mr_facts pre (hE σ e).2
    have hW := pre.W_eq
    have wl := pre.wle
    simp only [mrInit, checksC, setS, List.append_assoc, List.cons_append, List.nil_append]
    refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
    refine (h.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem).strM (m.of_upd u1)
      (hw.of_upd u1 (by decide) (by decide) (by decide)) (d := sI) (by decide) fun s2 h2 hw2 m2 g2 => ?_
    refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
    refine (h2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem).strM (m2.of_upd u3)
      (hw2.of_upd u3 (by decide) (by decide) (by decide)) (d := sUni) (by decide) fun s4 h4 hw4 m4 g4 => ?_
    refine wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
    have r9 : ∀ t : State, Ws t P.B P.Z P.W nArr → t.gpr .r9 = BitVec.ofNat 32 P.W := fun t ht => ht.r9
    have hw5 := hw4.of_upd u5 (by decide) (by decide) (by decide)
    have q5 := r9 _ hw5
    have b1 := VG.Proof.Rsa.b2n_le (decide (P.W < 120)); have b2 := VG.Proof.Rsa.b2n_le (decide (P.W < 46))
    have b3 := VG.Proof.Rsa.b2n_le (decide (P.W < 18)); have b4 := VG.Proof.Rsa.b2n_le (decide (P.W < 16))
    have b5 := VG.Proof.Rsa.b2n_le (decide (P.W < 14))
    refine ltAdd_ok (x := 3) q5 (by omega) (by decide) (by rw [u5.gpr]; rfl) (by decide) fun s6 k6 m6 v6 => ?_
    have q6 : s6.gpr .r9 = BitVec.ofNat 32 P.W := by rw [k6.gpr _ (by decide), q5]
    refine ltAdd_ok q6 (by omega) (by decide) v6 (by omega) fun s7 k7 m7 v7 => ?_
    have q7 : s7.gpr .r9 = BitVec.ofNat 32 P.W := by rw [k7.gpr _ (by decide), q6]
    refine ltAdd_ok q7 (by omega) (by decide) v7 (by omega) fun s8 k8 m8 v8 => ?_
    have q8 : s8.gpr .r9 = BitVec.ofNat 32 P.W := by rw [k8.gpr _ (by decide), q7]
    refine ltAdd_ok q8 (by omega) (by decide) v8 (by omega) fun s9 k9 m9 v9 => ?_
    have q9 : s9.gpr .r9 = BitVec.ofNat 32 P.W := by rw [k9.gpr _ (by decide), q8]
    refine ltAdd_ok q9 (by omega) (by decide) v9 (by omega) fun s10 k10 m10 v10 => ?_
    have q10 : s10.gpr .r9 = BitVec.ofNat 32 P.W := by rw [k10.gpr _ (by decide), q9]
    have k10' : Rest [.r1, .r2] s5 s10 := k6.trans (k7.trans (k8.trans (k9.trans k10)))
    refine wp_dp (op2_imm (by decide)) fun s11 u11 => wp_mov (op2_lsr (by decide)) fun s12 u12 =>
      wp_mov (op2_imm (by decide)) fun s13 u13 => wp_mul fun s14 u14 => wp_dp (op2_reg _ _) fun s15 u15 => ?_
    have k15 : Rest [.r1, .r2, .r3] s4 s15 := (u5.rest (by simp)).trans ((k10'.mono (by simp)).trans
      ((u11.rest (by simp)).trans ((u12.rest (by simp)).trans ((u13.rest (by simp)).trans ((u14.rest (by simp)).trans
      (u15.rest (by simp)))))))
    have mm15 : s15.mem = s4.mem := by rw [u15.mem, u14.mem, u13.mem, u12.mem, u11.mem, m10, m9, m8, m7, m6, u5.mem]
    have b12 : (s12.gpr .r2).toNat = b2n (decide (P.W < 12)) := by
      rw [u12.gpr, u11.gpr, dpVal, q10]
      exact lt_bit (by omega) (by decide)
    have v15 : s15.gpr .r1 = BitVec.ofNat 32 (checksW P.w) := by
      rw [u15.gpr, dpVal, u14.other _ (by decide), u13.other _ (by decide), u12.other _ (by decide),
        u11.other _ (by decide), v10, u14.gpr, u13.gpr, u13.other _ (by decide)]
      apply BitVec.eq_of_toNat_eq
      have hb := VG.Proof.Rsa.b2n_le (decide (P.W < 12))
      rw [BitVec.toNat_add, BitVec.toNat_mul, b12, ofNat_toNat_lt (by
        have := VG.Proof.Rsa.b2n_le (decide (P.W < 120)); have := VG.Proof.Rsa.b2n_le (decide (P.W < 46))
        have := VG.Proof.Rsa.b2n_le (decide (P.W < 18)); have := VG.Proof.Rsa.b2n_le (decide (P.W < 16))
        have := VG.Proof.Rsa.b2n_le (decide (P.W < 14)); omega)]
      have := checks_cmp P.w (by have := pre.w4; omega)
      rw [← hW] at this
      rw [ofNat_toNat_lt (by have := VG.Proof.RsaKeyGen.checksW_le P.w; omega)]
      have := VG.Proof.RsaKeyGen.checksW_le P.w
      simp only [show (19 : BitVec 32).toNat = 19 from rfl]
      omega
    refine (h4.of_rest k15 mm15).strM (m4.of_rest k15 mm15) (hw4.rest k15) (d := sChk) (by decide)
      fun t ht hwt mt _ => WP.block_nil ⟨by omega, Nat.le_refl _, ?_, ⟨e, ?_, hwt⟩, mt⟩
    · rw [Nat.sub_self, Nat.add_sub_cancel]
      have z := VG.Proof.RsaKeyGen.mrAt_zero (c := cv P σ) (ch := chP P) (a := taP P σ) (m := tmP P σ) fl fw
        (by have := pre.k1; omega) (by rw [rB_length]; exact (hE σ e).2.1)
      rw [rB_length, ← resP, ← fs] at z
      exact z
    · rw [v15, ofNat_toNat_lt (by have := VG.Proof.RsaKeyGen.checksW_le P.w; omega)] at ht
      refine ht.mono (fun j hj => ⟨hj, rfl⟩) fun j hj => ⟨by mem_sub, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      have v1 : (s1.gpr .r1).toNat = 1 := by rw [u1.gpr]; rfl
      have v3 : (s3.gpr .r1).toNat = 0 := by rw [u3.gpr]; rfl
      rcases hj with rfl | rfl | rfl | rfl
      · simp (config := {decide := true}) only [upd, ↓reduceIte, VI, v3, Nat.sub_self, VG.Proof.RsaKeyGen.mrS]
      · simp (config := {decide := true}) only [upd, ↓reduceIte, VI, v1, Nat.sub_self, VG.Proof.RsaKeyGen.mrS]
      · simp (config := {decide := true}) only [upd, ↓reduceIte, VI, V3, V2, V1, V0, Nat.sub_self]; omega
      · simp (config := {decide := true}) only [upd, ↓reduceIte, VI]

end

end VG.Proof.RsaKeyGen.Arm.Cand
