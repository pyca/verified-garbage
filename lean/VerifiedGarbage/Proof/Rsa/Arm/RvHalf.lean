module

public import VerifiedGarbage.Proof.Rsa.Arm.RvCnt
public import VerifiedGarbage.Proof.Rsa.RecoverMath
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: a halving of `m` (`halfBody_ok`)

`HI P σ k`: after `k` halvings, array `wR` (with `W` words) holds the first
of `halveStep^[k] (m, 0)`, the header word `sTc` its second, and `sCnt` the
halvings left, `c - k`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (halveStep)

/-- `(m, t)` after `k` halvings. -/
abbrev hvs (P : RP) (σ : State) (k : Nat) : Nat × Nat := halveStep^[k] (mv P σ, 0)

def AWh (P : RP) (σ : State) (k : Nat) : Nat → Nat := fun _ => (hvs P σ k).1
def Vh (P : RP) (σ : State) (k : Nat) : Nat → Nat := upd (upd (fun _ => 0) sTc (hvs P σ k).2) sCnt (P.c - k)

/-- After `k` halvings. -/
def HI (P : RP) (σ : State) (k : Nat) (s : State) : Prop :=
  KS P σ (Aload P σ) [aN] (AWh P σ k) [wR] (Vh P σ k) [sTc, sCnt] s ∧ Ws s P.B P.Z P.W 22

theorem hvs_le (P : RP) (σ : State) (k : Nat) : (hvs P σ k).2 ≤ k := by
  induction k with
  | zero => exact Nat.le_of_eq rfl
  | succ k ih =>
    have ih' : (halveStep^[k] (mv P σ, 0)).2 ≤ k := ih
    show (halveStep^[k + 1] (mv P σ, 0)).2 ≤ k + 1
    rw [Function.iterate_succ_apply']
    generalize halveStep^[k] (mv P σ, 0) = st at ih' ⊢
    unfold halveStep
    split
    · show st.2 + 1 ≤ k + 1; omega
    · show st.2 ≤ k + 1; omega

theorem hvs_succ (P : RP) (σ : State) (k : Nat) :
    hvs P σ (k + 1) = halveStep (hvs P σ k) := by rw [hvs, Function.iterate_succ_apply']

theorem halfBody_ok {P : RP} {σ s : State} {k : Nat} (h : HI P σ k s) (hk : k < P.c) :
    WP isa halfBody s fun t => HI P σ (k + 1) t ∧ t.z = decide (P.c - (k + 1) = 0) := by
  obtain ⟨h, hw⟩ := h
  have k2 := h.bs.pre.k2; have el2 := h.bs.pre.el2; have dl2 := h.bs.pre.dl2
  have hc : P.c ≤ 16384 := by simp only [RP.c]; omega
  have ht := hvs_le P σ k
  generalize eR : (hvs P σ k).1 = R at *
  generalize eT : (hvs P σ k).2 = T at *
  have aR : AWh P σ k wR = R := eR
  have vT : Vh P σ k sTc = T := by simp [Vh, upd, sTc, sCnt, eT]
  have vC : Vh P σ k sCnt = P.c - k := by simp [Vh, upd]
  have aW : AWh P σ k = fun _ => R := funext fun _ => eR
  rw [aW] at h
  unfold halfBody
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy_W hw (o := wU) (a := wR) (by decide) (by simp) (by decide)
    (by simp only [List.mem_singleton]; rintro j rfl; decide)) fun s1 ⟨h1, hw1, _⟩ => ?_)
  rw [upd_noop rfl] at h1
  refine WP.seq (WP.mono (h1.copy_W hw1 (o := wH) (a := wR) (by decide) (by simp) (by decide)
    (by simp only [List.mem_singleton]; rintro j rfl; decide)) fun s2 ⟨h2, hw2, _⟩ => ?_)
  rw [upd_noop rfl] at h2
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s3 u3 => WP.block_nil ?_)
  obtain ⟨h3, hw3⟩ := h2.reg hw2 (u3.rest (ws := [.r11]) (by simp)) u3.mem
  refine WP.seq (WP.mono (h3.half_W hw3 (j := wH) (by simp) (by rw [u3.gpr]; rfl)
    (by simp only [List.mem_singleton]; rintro j rfl; decide)) fun s4 ⟨h4, hw4, _⟩ => ?_)
  refine WP.seq ?_
  unfold halfBit
  refine h4.bitOf_W hw4 (j := wR) (by simp) (by decide) fun s5 h5 hw5 _ => ?_
  have b5 : upd (fun _ => R) wH (R / 2) wR % 2 = R % 2 := by rw [upd_ne _ _ (by decide)]
  rw [b5] at h5
  refine h5.ldrSlot hw5 (d := sBit) (r := .r1) (by simp) (by decide) fun s6 h6 hw6 u6 => ?_
  refine wp_dp (op2_imm (by decide)) fun s7 u7 => ?_
  obtain ⟨h7, hw7⟩ := h6.reg hw6 (u7.rest (ws := [.r1]) (by simp)) u7.mem
  refine h7.strSlot hw7 (d := sBit) (r := .r1) (by decide) fun s8 h8 hw8 g8 _ => ?_
  have ev : (s7.gpr .r1).toNat = 1 - R % 2 := by
    rw [u7.gpr, dpVal, u6.gpr, upd_self,
      bv_xor_bits (by rw [BitVec.toNat_ofNat]; omega) (by decide), BitVec.toNat_ofNat]
    simp only [show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  rw [ev] at h8
  refine h8.ldrSlot hw8 (d := sTc) (r := .r2) (by simp) (by decide) fun s9 h9 hw9 u9 => ?_
  refine wp_dp (op2_reg _ _) fun s10 u10 => ?_
  obtain ⟨h10, hw10⟩ := h9.reg hw9 (u10.rest (ws := [.r2]) (by simp)) u10.mem
  refine h10.strSlot hw10 (d := sTc) (r := .r2) (by decide) fun s11 h11 hw11 _ _ => WP.block_nil ?_
  have tv : (s10.gpr .r2).toNat = T + (1 - R % 2) := by
    rw [u10.gpr, dpVal, u9.gpr, u9.other .r1 (by decide), g8,
      show upd (upd (Vh P σ k) sBit (R % 2)) sBit (1 - R % 2) sTc = T by
        rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), vT]]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, ev]
    omega
  rw [tv] at h11
  refine WP.seq (WP.mono (h11.sel_W hw11 (o := wR) (a := wU) (b := wH) (sl := sBit) (by decide) (by simp) (by simp)
    (by decide) (by decide) (by simp) (by rw [upd_ne _ _ (by decide), upd_self]; omega)
    (by simp only [List.mem_singleton]; rintro j rfl; decide)) fun s12 ⟨h12, hw12, _⟩ => ?_)
  have c12 : upd (upd (upd (Vh P σ k) sBit (R % 2)) sBit (1 - R % 2)) sTc (T + (1 - R % 2)) sCnt = P.c - k := by
    rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide), vC]
  refine WP.mono (h12.cntNext_ok hw12 (by simp) (by rw [c12]; omega) (by rw [c12]; omega))
    fun t ⟨ht, hwt, zt⟩ => ⟨⟨?_, hwt⟩, ?_⟩
  · have hs := hvs_succ P σ k
    rw [show hvs P σ k = (R, T) from Prod.ext eR eT] at hs
    refine ht.mono (fun j hj => ⟨by simpa using hj, rfl⟩) (fun j hj => ?_) (fun d hd => ?_)
    · simp only [List.mem_singleton] at hj; subst hj
      refine ⟨by simp, ?_⟩
      have sv : upd (upd (upd (Vh P σ k) sBit (R % 2)) sBit (1 - R % 2)) sTc (T + (1 - R % 2)) sBit =
          1 - R % 2 := by rw [upd_ne _ _ (by decide), upd_self]
      simp only [AWh, hs, halveStep]
      rw [upd_self, sv, upd_ne (fun _ => R) (R / 2) (show wU ≠ wH by decide), upd_self]
      by_cases e : R % 2 = 0
      · simp only [e, ite_true]; split <;> omega
      · simp only [e, ite_false]; split <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · refine ⟨by simp, ?_⟩
        rw [upd_ne _ _ (by decide), upd_self]
        simp only [Vh, hs, halveStep]
        rw [upd_ne _ _ (by decide), upd_self]
        by_cases e : R % 2 = 0
        · simp only [e, ite_true]
        · simp only [e, ite_false]; omega
      · refine ⟨by simp, ?_⟩
        rw [upd_self, c12]
        simp only [Vh, upd_self]
        omega
  · rw [zt, c12]; simp only [decide_eq_decide]; omega

end VG.Proof.Rsa.Arm.Recover
