module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Trial
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Stage
import VerifiedGarbage.Proof.Dsa.Generation.Trial
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint4
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Instr
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Vals

/-! # A candidate on ARMv7: trial division (`trial_vp`)

From `S1`: the table written over the key arrays 22–48, trial division by
its primes, and the header word `sTr :=` whether one divides `c`, which is
`obviouslyComposite` (`trialAny_eq`): the stage `S2`, with Z iff not.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Impl.RsaKeyGen VG.Proof.RsaKeyGen
open VG.Proof.Rsa (b2n)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {P : CP}

/-- `c`'s low `W − 2` words are `c`. -/
theorem val32_c {σ s : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS P σ A live V ls s) (hc : aC ∈ live) (hA : A aC = cv P σ) :
    val32 s.mem (State.addr P.B) (arr P.W aC) (P.W - 2) = cv P σ := by
  have pre := h.pre
  have e := h.arrs aC hc
  rw [hA] at e
  have hW := pre.W_eq
  have hL := pre.L_eq
  have hcv := (cv_shape (σ := σ) pre).2.2
  have ap := val32_append s.mem (State.addr P.B) (arr P.W aC) (P.W - 2) 2
  rw [show P.W - 2 + 2 = P.W by omega_arith] at ap
  simp only [num] at e
  have lo := val32_lt s.mem (State.addr P.B) (arr P.W aC) (P.W - 2)
  have p : 2 ^ (8 * P.L) = 2 ^ (32 * (P.W - 2)) := by congr 1; omega_arith
  rw [p] at hcv
  rw [e] at ap
  generalize val32 s.mem (State.addr P.B) (arr P.W aC) (P.W - 2) = x at *
  generalize val32 s.mem (State.addr P.B) (arr P.W aC + 4 * (P.W - 2)) 2 = y at *
  have : y = 0 := by
    by_contra hy
    have : 2 ^ (32 * (P.W - 2)) * 1 ≤ 2 ^ (32 * (P.W - 2)) * y := Nat.mul_le_mul_left _ (by omega_arith)
    omega_arith
  subst this; omega_arith

theorem compv_eq {σ : State} (pre : In P σ) :
    tr (2 * nT P.W) (cv P σ) = compv P σ := by
  have hW := pre.W_eq
  have hw := pre.w4
  have hL := pre.L_eq
  have sz := pre.sizes
  have h8 : 8161 < cv P σ := by
    have := (cv_shape (σ := σ) pre).2.1
    have : 2 ^ 14 ≤ 2 ^ (P.bits - 1) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    omega_arith
  have hpol : 1024 < P.bits ↔ 16 < P.w := by
    have hw' : P.w = Impl.Dsa.Arm.ProbablePrime.words P.bits := by have := pre.L; simp only [CP.w]; omega_arith
    rw [hw']; exact VG.Proof.Dsa.Generation.trial_policy pre.bits
  have e := VG.Proof.Dsa.Generation.trialAny_dsa (w := P.w) h8 hpol
  unfold compv
  rw [← e]
  unfold tr trialAny nT
  by_cases h : 17 ≤ P.w
  · rw [ite_eq_left (show 35 ≤ P.W by omega_arith), ite_eq_left h]
  · rw [ite_eq_right (show ¬ 35 ≤ P.W by omega_arith), ite_eq_right h]

theorem trial_vp {E : State → Prop} :
    VP (S1 P E) (seqs trial) (fun σ s => S2 P E σ s ∧ s.z = decide (V2 P σ sTr = 0)) :=
  VP.kv trial_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    have pre := h.pre
    have hW := pre.W_eq
    have wge := pre.wge
    have hfit := pre.fits
    refine WP.assoc (WP.seq (WP.mono (table_ok hw wge) fun s1 ⟨hw1, keep1, tab1, sp1, rd1, wr1⟩ => ?_))
    have h1 : KS P σ (A0 P σ) L1 (V1 P σ) [sUsed] s1 :=
      h.core keep1 (fun j hj => by simp only [tabJs, List.mem_range'_1] at hj; simp only [nArr]; omega_arith)
        (by simp) sp1 rd1 wr1
        (h.arrs_keep keep1 (fun j hj hj' => by
          simp only [tabJs, List.mem_range'_1] at hj'
          simp only [L1, List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl | rfl | rfl <;> simp [aTwo, aOne, aC, aZero] at hj' <;> omega_arith) (by simp))
        (h.sl_keep keep1 (by simp) (by simp)) h.live_lt h.ls_ok
    have hc := val32_c h1 (by simp) (by simp (config := {decide := true}) only [A0, upd, ↓reduceIte])
    -- The count, `r11 := 0`, and the table's address.
    refine WP.seq ?_
    simp only [bigW, List.cons_append, List.nil_append]
    refine wp_subsC (op2_imm (by decide)) fun s3 u3 c3 => wp_movC (op2_imm (by decide)) fun s4 u4 c4 =>
      wp_adc (op2_imm (by decide)) fun s5 u5 => wp_mov (op2_lsl (by decide)) fun s6 u6 =>
        wp_dp (op2_imm (by decide)) fun s7 u7 => wp_mov (op2_imm (by decide)) fun s8 u8 => ?_
    have k8 : Rest [.r1, .r11, .lr] s1 s8 := (u3.rest (by simp)).trans ((u4.rest (by simp)).trans
      ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans ((u7.rest (by simp)).trans (u8.rest (by simp))))))
    have m8 : s8.mem = s1.mem := by rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem]
    have hw8 := hw1.rest k8
    have lr8 : s8.gpr .lr = BitVec.ofNat 32 (nT P.W) := by
      rw [u8.other _ (by decide), u7.gpr, dpVal, u6.gpr, u5.gpr, u4.gpr, c4, c3, hw1.r9]
      have : P.W < 2 ^ 32 := by have := pre.wle; omega_arith
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, ofNat_toNat_lt this]
      simp only [nT]
      by_cases h35 : 35 ≤ P.W <;> simp [h35] <;> omega_arith
    refine ptr_ok hw8 (r := .r12) (j := aTab) (by decide) (by decide) fun s9 p9 k9 m9 hw9 => WP.block_nil ?_
    have to0 : TO P.B P.Z P.W s1.mem s9 0 s9 := ⟨hw9, by rw [m9, m8], Rest.refl _ _,
      by rw [p9, Nat.mul_zero, Nat.add_zero], by rw [k9.gpr _ (by decide), lr8, Nat.sub_zero],
      by rw [k9.gpr _ (by decide), u8.gpr]; rfl⟩
    refine WP.seq (WP.mono (trialLoop_ok to0 wge (by omega_arith) hfit tab1) fun s10 t10 => ?_)
    obtain ⟨hw10, m10, k10, -, -, r1110⟩ := t10
    have h10 : KS P σ (A0 P σ) L1 (V1 P σ) [sUsed] s10 :=
      h1.of_rest ((k8.mono (by simp)).trans ((k9.mono (by simp)).trans k10)) m10
    rw [hc] at r1110
    refine h10.str hw10 (d := sTr) (by decide) fun s11 h11 hw11 m11 => ?_
    refine wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil ?_
    have v : (s10.gpr .r11).toNat = b2n (compv P σ) := by
      rw [r1110, compv_eq pre, ofNat_toNat_lt (VG.Proof.RsaKeyGen.Arm.Key.b2n_lt _)]
    refine ⟨⟨e, (h11.of_rest (f.rest []) f.mem).mono (fun j hj => ⟨hj, rfl⟩) fun d hd => ⟨?_, ?_⟩,
      hw11.of (by rw [f.gpr]) (by rw [f.gpr]) (by rw [f.gpr]) f.wr⟩, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; omega_arith
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · rw [upd_self, v]; simp only [V2, upd_self]
      · rw [upd_ne _ _ (by decide)]; simp (config := {decide := true}) only [V2, upd, ↓reduceIte]
    · rw [z, m11.gpr, r1110, compv_eq pre]
      simp only [V2, upd_self]
      cases compv P σ <;> decide

end

end VG.Proof.Dsa.Arm.Prime
