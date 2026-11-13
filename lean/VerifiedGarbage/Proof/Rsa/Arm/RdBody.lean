module
-- separate module: the proof of Appendix C.2's body is split in a chain of modules, so that a change rebuilds only the modules after it
public import VerifiedGarbage.Proof.Rsa.Arm.RdSqrt
public import VerifiedGarbage.Proof.Rsa.Arm.RdStore
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
import VerifiedGarbage.Proof.Rsa.RecoverRoot

import VerifiedGarbage.Proof.Rsa.Arm.Stage.Numbers
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Prod
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Slots
import VerifiedGarbage.Proof.Rsa.Arm.RdRows
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Fail
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # `vg_rsa_recover_primes_det` on ARMv7: the body (`bodyD_vp`)

The stages with Appendix C.2's model's steps (`twoStep`, `prodStep`,
`Proof/Rsa/RecoverDet.lean`), whose result is the model's (`result`, whose
bit-by-bit square root `sqrtStep` is `isqrt` wherever the mask can be set:
`okV_result`, by `RecoverRoot.root_bridge`), hence `recoverDet`'s (`model_correct`); the factors written
out under the mask (`ResD`). The only module of this port that imports the
model.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.RecoverDet
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Recover
open VG.Impl.Rsa.Arm.Keys hiding aT1 aT2 aT3 aT4
open VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverDet
open VG.Impl.Rsa.Arm.Recover (nArr aW)
open VG.Proof.Rsa (sub32 b2n)
open VG.Proof.Rsa.RecoverDet (twoStep prodStep sqrtStep wsub)

section
variable {P : RP}

/-- The model's steps. -/
abbrev fS (P : RP) : Nat × Nat × Nat → Nat × Nat × Nat := twoStep (32 * P.W)
abbrev gS (P : RP) : Nat × Nat × Nat → Nat × Nat × Nat := prodStep (32 * P.W)

theorem twoF : TwoF P (fS P) := fun _ _ _ => rfl
theorem prodF : ProdF P (gS P) := fun _ _ _ => rfl

theorem n_lt' {σ : State} (pre : In P σ) : P.n < 2 ^ (32 * P.w) := by
  have := bytes_lt σ.mem (State.addr P.nP) P.K
  rw [pre.nB] at this
  have kw := pre.sizes.kw
  exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))

theorem valid_facts' (hv : Spec.Rsa.modulusValid P.n P.K = true) (hk : 2 ≤ P.K) : P.n % 2 = 1 ∧ 3 ≤ P.n := by
  simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
  have h1 := hv.1.1.1
  have h2 := hv.2
  have : 256 ^ 1 ≤ 256 ^ (P.K - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have : (256 : Nat) ^ 1 = 256 := rfl
  omega

/-- `u` is odd after the halvings. -/
theorem u_odd (hv : Spec.Rsa.modulusValid P.n P.K = true) {σ : State} (pre : In P σ) :
    (ts P (fS P) σ (32 * P.w)).1 % 2 = 1 := by
  obtain ⟨odd, three⟩ := valid_facts' hv (by have := pre.k1; omega)
  have nl := n_lt' pre
  have xl : xV P σ % 2 ^ (32 * P.w) < 2 ^ (32 * P.W) :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by simp only [RP.W]; omega))
  have un : sub32 P.w P.n 1 = P.n - 1 := VG.Proof.Rsa.sub32_one (by omega) nl
  simp only [ts, fS]
  rw [un, (VG.Proof.Rsa.RecoverDet.twos_proj (32 * P.W) (32 * P.w) _ _ _ (xV P σ % 2 ^ (32 * P.w))).1]
  exact (VG.Proof.Rsa.RecoverDet.twos_iter (by omega) (by omega) xl).1

theorem gV_eq {σ : State} : AG P (fS P) σ aG =
    Nat.gcd (ts P (fS P) σ (32 * P.w)).1 (ts P (fS P) σ (32 * P.w)).2.1 := by
  simp only [AG, gV]; rd_ev
  split
  · rename_i h; rw [h, Nat.gcd_one_left]
  · exact Nat.gcd_comm _ _

theorem aV_eq {σ : State} : aV P (fS P) (gS P) σ = VG.Proof.Rsa.RecoverDet.aOf (32 * P.w) (32 * P.W) P.n (Mv P σ) := by
  have hX : AWG P (fS P) σ wX3 = (ts P (fS P) σ (32 * P.w)).2.2 := by simp only [AWG]; rd_ev
  simp only [aV, pr, gV_eq, hX]
  rfl

/-- The model's mask and factors, its square root still the bit model's (`sqrtStep`). -/
theorem result_bits {σ : State} :
    VG.Proof.Rsa.RecoverDet.result (32 * P.w) (32 * P.W) P.n (Mv P σ) (qV P (fS P) (gS P) σ) (remV P (fS P) (gS P) σ) =
      let r := (sqrtStep (32 * P.w) (32 * P.W))^[16 * P.W] (xRV P (fS P) (gS P) σ, 0, 0)
      if okDEv P σ && decide (aV P (fS P) (gS P) σ / P.n < P.n) && decide (remV P (fS P) (gS P) σ = 0) &&
          ok4v P (fS P) (gS P) σ && decide (r.2.1 = 0)
      then some ((bV P (fS P) (gS P) σ + r.2.2) % 2 ^ (32 * P.w) / 2, sub32 P.w (bV P (fS P) (gS P) σ) r.2.2 / 2)
      else none := by
  have w1 : 1 < 2 ^ (32 * P.w) := Nat.one_lt_two_pow (by simp only [RP.w]; omega)
  have ql : qV P (fS P) (gS P) σ < 2 ^ (32 * P.w) :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (Nat.two_pow_pos _))
  have hb : bV P (fS P) (gS P) σ = (qV P (fS P) (gS P) σ + 1) % 2 ^ (32 * P.w) := sub32_neg ql w1
  simp only [VG.Proof.Rsa.RecoverDet.result, VG.Proof.Rsa.RecoverDet.stage2, VG.Proof.Rsa.RecoverDet.bOf, VG.Proof.Rsa.RecoverDet.rootOf, VG.Proof.Rsa.RecoverDet.ok4Of,
    VG.Proof.Rsa.RecoverDet.xOf, VG.Proof.Rsa.RecoverDet.sqOf, VG.Proof.Rsa.RecoverDet.fourN, VG.Proof.Rsa.RecoverDet.ltOf, VG.Proof.Rsa.RecoverDet.mOf, VG.Proof.Rsa.RecoverDet.okDE,
    VG.Proof.Rsa.RecoverDet.deX]
  simp only [← aV_eq, ← hb, show 32 * P.W / 2 = 16 * P.W by omega, Bool.and_assoc]
  rfl

open VG.Spec.Rsa (isqrt) in
/-- Where the mask can be set, the bit model's root is `isqrt` (`RecoverRoot.root_bridge`), given that the
divisions are the model's: `m + 1` and `n - r` (`hm`, `hd`). -/
theorem okV_result {σ : State} (hn : 8 * (P.n + 2) ≤ 2 ^ (32 * P.w)) (n3 : 3 ≤ P.n)
    (hm : VG.Proof.Rsa.RecoverDet.m1Of (32 * P.w) (32 * P.W) P.n (Mv P σ) = m1R P (fS P) (gS P) σ)
    (hd : VG.Proof.Rsa.RecoverDet.dOf (32 * P.w) (32 * P.W) P.n (Mv P σ) = dV P (fS P) (gS P) σ) :
    VG.Proof.Rsa.RecoverDet.result (32 * P.w) (32 * P.W) P.n (Mv P σ) (qV P (fS P) (gS P) σ) (remV P (fS P) (gS P) σ) =
      if okV P (fS P) (gS P) σ then some (pV P (fS P) (gS P) σ, qV' P (fS P) (gS P) σ)
      else none := by
  rw [result_bits]
  simp only [okV]
  by_cases hlt : aV P (fS P) (gS P) σ / P.n < P.n
  swap
  · simp only [hlt, decide_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  by_cases h4 : ok4v P (fS P) (gS P) σ = true
  swap
  · simp only [Bool.eq_false_iff.mpr h4, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have w1 : 1 < 2 ^ (32 * P.w) := Nat.one_lt_two_pow (by simp only [RP.w]; omega)
  -- the model's quotient
  have ltT : VG.Proof.Rsa.RecoverDet.ltOf (32 * P.w) (32 * P.W) P.n (Mv P σ) = true := by
    simp only [VG.Proof.Rsa.RecoverDet.ltOf, VG.Proof.Rsa.RecoverDet.mOf, ← aV_eq]; exact decide_eq_true hlt
  have m1e : VG.Proof.Rsa.RecoverDet.m1Of (32 * P.w) (32 * P.W) P.n (Mv P σ) = aV P (fS P) (gS P) σ / P.n + 1 := by
    rw [VG.Proof.Rsa.RecoverDet.m1Of, VG.Proof.Rsa.RecoverDet.mOf, ← aV_eq,
      Nat.mod_eq_of_lt (show aV P (fS P) (gS P) σ / P.n < 2 ^ (32 * P.w) by omega), Nat.mod_eq_of_lt (by omega)]
  have m1pos : m1R P (fS P) (gS P) σ ≠ 0 := by rw [← hm, m1e]; exact Nat.succ_ne_zero _
  have hq : qV P (fS P) (gS P) σ = VG.Proof.Rsa.RecoverDet.dOf (32 * P.w) (32 * P.W) P.n (Mv P σ) /
      VG.Proof.Rsa.RecoverDet.m1Of (32 * P.w) (32 * P.W) P.n (Mv P σ) := by
    simp only [qV, m1V, m1pos, ↓reduceIte]; rw [hd, hm]
  have ql : qV P (fS P) (gS P) σ < 2 ^ (32 * P.w) :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (Nat.two_pow_pos _))
  have hb : bV P (fS P) (gS P) σ = VG.Proof.Rsa.RecoverDet.bOf (32 * P.w) (qV P (fS P) (gS P) σ) :=
    sub32_neg ql w1
  -- the root
  obtain ⟨ry, rz, rl⟩ := VG.Proof.Rsa.RecoverDet.root_bridge (de := Mv P σ) n3 hn (by simp only [RP.W]; omega)
    (by omega) ltT hq (by rw [← hb]; exact h4)
  rw [← hb] at ry rz rl
  have hr : VG.Proof.Rsa.RecoverDet.rootOf (32 * P.w) (32 * P.W) P.n (bV P (fS P) (gS P) σ) =
      (sqrtStep (32 * P.w) (32 * P.W))^[16 * P.W] (xRV P (fS P) (gS P) σ, 0, 0) := by
    simp only [VG.Proof.Rsa.RecoverDet.rootOf, show 32 * P.W / 2 = 16 * P.W by omega]; rfl
  have hx : VG.Proof.Rsa.RecoverDet.xOf (32 * P.w) (32 * P.W) P.n (bV P (fS P) (gS P) σ) = xRV P (fS P) (gS P) σ :=
    rfl
  rw [hr, hx] at ry rz
  rw [hx] at rl
  simp only [ry]
  have e0 : ((sqrtStep (32 * P.w) (32 * P.W))^[16 * P.W] (xRV P (fS P) (gS P) σ, 0, 0)).2.1 = 0 ↔
      rmV P (fS P) (gS P) σ = 0 := by
    have := VG.Proof.Rsa.RecoverDet.isqrt_sq_le (xRV P (fS P) (gS P) σ)
    rw [rz]; simp only [rmV]; omega
  simp only [e0, pV, qV', yV, Nat.mod_eq_of_lt rl]

theorem pow_le_w {k : Nat} (hk : k ≤ 8 * P.K + 64) : 2 ^ k ≤ 2 ^ (32 * P.w) :=
  Nat.pow_le_pow_right (by decide) (by simp only [RP.w, RP.w6]; omega)

theorem rd_eq (hv : Spec.Rsa.modulusValid P.n P.K = true) {σ : State} (pre : In P σ) (he : P.el ≤ 8) :
    Spec.Rsa.recoverDet P.n P.e (dv P σ) =
      if okV P (fS P) (gS P) σ then some (pV P (fS P) (gS P) σ, qV' P (fS P) (gS P) σ)
      else none := by
  obtain ⟨odd, three⟩ := valid_facts' hv (by have := pre.k1; omega)
  have nK : P.n < 2 ^ (8 * P.K) := by have := bytes_lt σ.mem (State.addr P.nP) P.K; rwa [pre.nB] at this
  have hn : 8 * (P.n + 2) ≤ 2 ^ (32 * P.w) := by
    have p2 : 2 ≤ 2 ^ (8 * P.K) := Nat.le_self_pow (by have := pre.k1; omega) 2
    have : 2 ^ (8 * P.K + 4) = 2 ^ (8 * P.K) * 16 := by rw [Nat.pow_add]
    have := pow_le_w (P := P) (k := 8 * P.K + 4) (by omega)
    omega
  have hde : dv P σ * P.e < 2 ^ (32 * P.w) := by
    have hd : dv P σ < 2 ^ (8 * P.dl) := bytes_lt σ.mem (State.addr P.dP) P.dl
    have hee : P.e < 2 ^ (8 * P.el) := by have := bytes_lt σ.mem (State.addr P.eP) P.el; rwa [pre.eB] at this
    calc dv P σ * P.e < 2 ^ (8 * P.dl) * 2 ^ (8 * P.el) := Nat.mul_lt_mul'' hd hee
      _ = 2 ^ (8 * P.dl + 8 * P.el) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ (32 * P.w) := pow_le_w (by have := pre.dl2; omega)
  have w1 : 1 < 2 ^ (32 * P.w) := Nat.one_lt_two_pow (by simp only [RP.w]; omega)
  have hlo : 256 ^ (P.K - 1) ≤ P.n := by
    simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, decide_eq_true_eq] at hv; exact hv.2
  obtain ⟨-, -, nn, -⟩ := n_facts pre.sizes hlo nK
  by_cases aok : aV P (fS P) (gS P) σ < 2 ^ (32 * (P.W - sA P))
  swap
  · -- `a` too wide for the shifted division: `m ≥ n`, and both are `none`.
    have hn0 : 0 < P.n := by omega
    have lt : ¬ aV P (fS P) (gS P) σ / P.n < P.n := fun h' => by
      have := (Nat.div_lt_iff_lt_mul hn0).mp h'; omega
    rw [← VG.Proof.Rsa.RecoverDet.model_correct (nb := 32 * P.w) (wb := 32 * P.W)
      (q := VG.Proof.Rsa.RecoverDet.dOf (32 * P.w) (32 * P.W) P.n (dv P σ * P.e) /
        VG.Proof.Rsa.RecoverDet.m1Of (32 * P.w) (32 * P.W) P.n (dv P σ * P.e))
      (rem := VG.Proof.Rsa.RecoverDet.dOf (32 * P.w) (32 * P.W) P.n (dv P σ * P.e) %
        VG.Proof.Rsa.RecoverDet.m1Of (32 * P.w) (32 * P.W) P.n (dv P σ * P.e))
      odd three hn hde (by simp only [RP.W]; omega) (by omega) fun _ => ⟨rfl, rfl⟩]
    have l2 : VG.Proof.Rsa.RecoverDet.ltOf (32 * P.w) (32 * P.W) P.n (dv P σ * P.e) = false := by
      simp only [VG.Proof.Rsa.RecoverDet.ltOf, VG.Proof.Rsa.RecoverDet.mOf]
      apply decide_eq_false
      rw [← show Mv P σ = dv P σ * P.e from rfl, ← aV_eq]; exact lt
    have o2 : okV P (fS P) (gS P) σ = false := by simp [okV, lt]
    simp only [VG.Proof.Rsa.RecoverDet.result, l2, Bool.and_false, Bool.false_and, o2, Bool.false_eq_true,
      ite_false]
  have ha0 : aV P (fS P) (gS P) σ % 2 ^ (32 * (P.W - sA P)) = aV P (fS P) (gS P) σ := Nat.mod_eq_of_lt aok
  have hm : VG.Proof.Rsa.RecoverDet.m1Of (32 * P.w) (32 * P.W) P.n (dv P σ * P.e) = m1R P (fS P) (gS P) σ := by
    rw [m1R, sub32_neg (Nat.mod_lt _ (Nat.two_pow_pos _)) w1, VG.Proof.Rsa.RecoverDet.m1Of,
      VG.Proof.Rsa.RecoverDet.mOf]
    simp only [mV, a0V, ha0]
    rw [← aV_eq]
  have hd : VG.Proof.Rsa.RecoverDet.dOf (32 * P.w) (32 * P.W) P.n (dv P σ * P.e) = dV P (fS P) (gS P) σ := by
    rw [VG.Proof.Rsa.RecoverDet.dOf, VG.Proof.Rsa.RecoverDet.rOf]
    simp only [dV, rV, a0V, ha0]
    rw [← aV_eq]; rfl
  rw [← VG.Proof.Rsa.RecoverDet.model_correct (nb := 32 * P.w) (wb := 32 * P.W)
    (q := qV P (fS P) (gS P) σ) (rem := remV P (fS P) (gS P) σ) odd three hn hde (by simp only [RP.W]; omega)
    (by omega) fun pos => ?_]
  · exact okV_result hn three hm hd
  rw [hm] at pos ⊢
  rw [hd]
  have : m1V P (fS P) (gS P) σ = m1R P (fS P) (gS P) σ := by simp only [m1V]; split <;> omega
  exact ⟨by rw [← this], by rw [← this]⟩

theorem pk_eq (hv : Spec.Rsa.modulusValid P.n P.K = true) {σ : State} (pre : In P σ) (he : P.el ≤ 8) :
    Spec.Rsa.primesKeyDet P.nB P.eB (dB P σ) =
      if okV P (fS P) (gS P) σ then
        some (Spec.Rsa.i2osp (pV P (fS P) (gS P) σ) P.K, Spec.Rsa.i2osp (qV' P (fS P) (gS P) σ) P.K)
      else none := by
  have hl : P.nB.length = P.K := by rw [← pre.nB]; simp [Spec.Rsa.bytesAt]
  simp only [Spec.Rsa.primesKeyDet, hl, show Spec.Rsa.os2ip P.nB = P.n from rfl, hv, ite_true]
  rw [show Spec.Rsa.os2ip P.eB = P.e from rfl, show Spec.Rsa.os2ip (dB P σ) = dv P σ from rfl, rd_eq hv pre he]
  cases okV P (fS P) (gS P) σ <;> rfl

theorem factors_lt (hv : Spec.Rsa.modulusValid P.n P.K = true) {σ : State} (pre : In P σ) (he : P.el ≤ 8)
    (ok : okV P (fS P) (gS P) σ = true) :
    pV P (fS P) (gS P) σ < 2 ^ (8 * P.K) ∧ qV' P (fS P) (gS P) σ < 2 ^ (8 * P.K) := by
  have e := rd_eq hv pre he
  simp only [ok, ↓reduceIte] at e
  have m := VG.Proof.Rsa.RecoverDet.recoverDet_mul e
  have nK : P.n < 2 ^ (8 * P.K) := by have := bytes_lt σ.mem (State.addr P.nP) P.K; rwa [pre.nB] at this
  obtain ⟨odd, three⟩ := valid_facts' hv (by have := pre.k1; omega)
  have p0 : 0 < pV P (fS P) (gS P) σ := Nat.pos_of_ne_zero fun h => by rw [h] at m; omega
  have q0 : 0 < qV' P (fS P) (gS P) σ := Nat.pos_of_ne_zero fun h => by rw [h] at m; omega
  constructor
  · exact Nat.lt_of_le_of_lt (by rw [← m]; exact Nat.le_mul_of_pos_right _ q0) nK
  · exact Nat.lt_of_le_of_lt (by rw [← m]; exact Nat.le_mul_of_pos_left _ p0) nK

theorem rcfgA : RCfg wA wX3 17 LG LWT := by
  constructor <;> decide

/-- The factors and the mask. -/
abbrev pF' (P : RP) : State → Nat := pV P (fS P) (gS P)
abbrev qF' (P : RP) : State → Nat := qV' P (fS P) (gS P)
abbrev okF' (P : RP) : State → Bool := okV P (fS P) (gS P)

/-! ## `d e` by rows of words -/

/-- The rows of `d e`: `⌈e_len / 4⌉`. -/
abbrev rE (P : RP) : Nat := (P.el + 3) / 4

/-- `cntE`: `4 R` from `sRows`. -/
theorem cntE_ok {V : Nat → Nat} {LS : List Nat} {R : Nat} (hd : sRows ∈ LS) (hv : V sRows = 4 * R) :
    CntOk P V LS cntE R := by
  intro t ht _ hsl rest Q k
  refine wp_ldrSlot ht (d := sRows) (by decide) fun u U => k u (U.rest (ws := [.r1]) (by simp)) U.mem ?_
  rw [U.gpr]
  have e := hsl sRows hd (by decide)
  rw [hv] at e
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  change (t.mem.readW (off (State.addr P.B) sRows) 32).toNat = _
  have l := (t.mem.readW (off (State.addr P.B) sRows) 32).isLt
  simp only [slot, w32] at e
  omega

/-- `d e` (wide `wM`), by a row for each of `e`'s words. -/
theorem prodW_vp {E : State → Prop} (hE : ∀ σ, E σ → In P σ) :
    VP (fun σ s => E σ ∧ LS P σ (Aload P σ) s) prodW
      (fun σ s => E σ ∧ KS P σ (Aload P σ) [VG.Impl.Rsa.Arm.Recover.aN] (AWp P σ)
        [VG.Impl.Rsa.Arm.Recover.wM, VG.Impl.Rsa.Arm.Recover.wZ] (fun _ => 0) [] s ∧ Ws s P.B P.Z P.W 22) := by
  simp only [prodW, rowsE, seqs]
  let L0 : List Nat := [VG.Impl.Rsa.Arm.Recover.aN, 2 * VG.Impl.Rsa.Arm.Recover.wE]
  let LW0 : List Nat := [VG.Impl.Rsa.Arm.Recover.wZ, VG.Impl.Rsa.Arm.Recover.wE, VG.Impl.Rsa.Arm.Recover.wD,
    VG.Impl.Rsa.Arm.Recover.wM, 14]
  let V1 : State → Nat → Nat := fun _ => upd (fun _ => 0) sRows (4 * rE P)
  refine VP.seq (G := Dk P E (Aload P) L0 (VG.Proof.Rsa.Arm.Recover.AW1 P) LW0 V1 [sRows] P.w nArr) (VP.seq
    (G := fun σ s => (E σ ∧ KS P σ (Aload P σ) L0 (VG.Proof.Rsa.Arm.Recover.AW1 P σ) LW0 (fun _ => 0) [] s ∧ Ws s P.B P.Z P.w nArr) ∧
      s.gpr .r1 = BitVec.ofNat 32 P.el) ?_ ?_) ?_
  -- `e_len`.
  · show VP _ (.block ([(Reg.r1, VG.Impl.Rsa.Arm.Recover.aoEl)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h⟩ => ?_
    · rw [h₁.2.bs.sp, h₁.2.bs.pre.sp, h₂.2.bs.sp, h₂.2.bs.pre.sp]
    · have K := VG.Proof.Rsa.Arm.Recover.LS.ksE h
      exact h.bs.ldrSp (o := VG.Impl.Rsa.Arm.Recover.aoEl) (by decide) (by decide) (by decide) fun t u =>
        WP.block_nil ⟨⟨e, K.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem (by decide),
          h.ws.of_upd u (by decide) (by decide) (by decide)⟩, u.gpr.trans h.bs.pre.aEl⟩
  -- `4 ⌈e_len / 4⌉` at `sRows`.
  · refine VP.taint [.r1, .r7, .r8, .r9] rowsE_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨⟨e, h, hv⟩, r1⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.2, h₂.2]
      · rw [h₁.1.2.2.r7, h₂.1.2.2.r7]
      · rw [h₁.1.2.2.r8, h₂.1.2.2.r8]
      · rw [h₁.1.2.2.r9, h₂.1.2.2.r9]
    have el2 := h.bs.pre.el2; have k2 := h.bs.pre.k2
    refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
    refine wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
    refine wp_mov (op2_lsl (by decide)) fun s4 u4 => ?_
    obtain ⟨h4, hv4⟩ := h.reg hv ((u2.rest (ws := [.r1]) (by simp)).trans ((u3.rest (ws := [.r1]) (by simp)).trans
      (u4.rest (ws := [.r1]) (by simp)))) (by rw [u4.mem, u3.mem, u2.mem])
    have g4 : s4.gpr .r1 = BitVec.ofNat 32 (4 * rE P) := by
      rw [u4.gpr, u3.gpr, u2.gpr, dpVal, r1]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_add, BitVec.toNat_ofNat, rE]
      have : (3 : BitVec 32).toNat = 3 := rfl
      omega
    refine h4.strSlot hv4 (d := sRows) (r := .r1) (by decide) fun t ht hvt _ _ => WP.block_nil ⟨e, ?_, hvt⟩
    rw [g4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [rE]; omega)] at ht
    exact ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  -- The rows, and the wide context.
  have rcfg : RCfg VG.Impl.Rsa.Arm.Recover.wM VG.Impl.Rsa.Arm.Recover.wD VG.Impl.Rsa.Arm.Recover.wE L0 LW0 := by
    constructor <;> decide
  refine VP.of_imp (p := 0 < rE P ∧ rE P ≤ P.w) (fun σ s ⟨e, h, _⟩ => by
    have := h.bs.pre.el1; have := h.bs.pre.el2; have kw := h.sizes.kw
    simp only [rE]; constructor <;> omega) fun ⟨pos, hR⟩ => ?_
  refine VP.seq (rowProdG_vp rcfg (by decide) (by decide) (fun σ _ => by
      rfl) pos hR
    (fun σ _ => cntE_ok (by simp) (by simp [V1, upd])) copyM_taint pRowAM_taint pRowBE_taint) ?_
  refine VP.dctx toW_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_
  rw [← List.append_nil toW]
  refine h.toW hv fun t ht hvt _ => WP.block_nil ⟨e, ht.mono (fun j hj => ⟨?_, ?_⟩) (fun j hj => ⟨?_, ?_⟩)
    (fun d hd => absurd hd (List.not_mem_nil)), hvt⟩
  · simp only [List.mem_singleton] at hj; subst hj; simp [L0]
  · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> simp [LW0]
  · have pre := hE σ e
    have hee : P.e < 2 ^ (8 * P.el) := by have := bytes_lt σ.mem (State.addr P.eP) P.el; rwa [pre.eB] at this
    have hd : dv P σ < 2 ^ (8 * P.dl) := bytes_lt σ.mem (State.addr P.dP) P.dl
    have sz := pre.sizes
    have := pre.el2; have := pre.dl2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · have e1 : Aload P σ (2 * VG.Impl.Rsa.Arm.Recover.wE) = P.e := rfl
      have e2 : VG.Proof.Rsa.Arm.Recover.AW1 P σ VG.Impl.Rsa.Arm.Recover.wD = dv P σ := rfl
      have e3 : AWp P σ VG.Impl.Rsa.Arm.Recover.wM = Mv P σ := rfl
      rw [upd_self, e1, e2, e3]
      have p1 : 2 ^ (8 * P.el) ≤ 2 ^ (32 * rE P) := Nat.pow_le_pow_right (by decide) (by simp only [rE]; omega)
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hee p1), Nat.mul_comm, Nat.mod_eq_of_lt]
      calc dv P σ * P.e < 2 ^ (8 * P.dl) * 2 ^ (8 * P.el) := Nat.mul_lt_mul'' hd hee
        _ = 2 ^ (8 * P.dl + 8 * P.el) := (Nat.pow_add _ _ _).symm
        _ ≤ 2 ^ (32 * P.W) := Nat.pow_le_pow_right (by decide) (by simp only [RP.W, RP.w, RP.w6]; omega)
    · simp [AWp, VG.Proof.Rsa.Arm.Recover.AW1, upd, VG.Impl.Rsa.Arm.Recover.wM, VG.Impl.Rsa.Arm.Recover.wZ, VG.Impl.Rsa.Arm.Recover.wE,
        VG.Impl.Rsa.Arm.Recover.wD]

theorem validD_vp [InvLaw] (hv : Spec.Rsa.modulusValid P.n P.K = true) (he : P.el ≤ 8) :
    VP (fun σ s => True ∧ Bs P σ s) VG.Impl.Rsa.Arm.RecoverDet.valid (FeD P (In P) (pF' P) (qF' P) (okF' P)) := by
  have hn0 : 0 < P.n := by
    simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv; omega
  have hn2 : 2 ≤ P.n := by
    simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv; omega
  simp only [VG.Impl.Rsa.Arm.RecoverDet.valid, seqs]
  rw [show (prodW : Prog isa) = prodW from rfl]
  refine (loads_vp (E := In P)).mono (fun σ s ⟨_, h⟩ => ⟨h.pre, h⟩) (fun _ _ h => h) |>.seq ?_
  refine (prodW_vp (E := In P) fun _ e => e).seq ?_
  refine VP.seq ?_ (storesD_vp (pF' P) (qF' P) (okF' P) (fun σ e ok => (factors_lt hv e he ok).1)
    (fun σ e ok => (factors_lt hv e he ok).2))
  simp only [det, seqs]
  refine VP.seq deMinus_vp (VP.seq (twosW_vp twoF hn2) (VP.seq (gcd_vp fun σ e => u_odd hv e) ?_))
  refine VP.seq (rowProd_vp rcfgA (by decide) (by decide) (fun σ _ => by simp only [AWG]; rd_up) copyA_taint
    pRowA_taint pRowBA_taint) ?_
  refine VP.seq (divA_vp prodF (fun σ e => ⟨e.sizes, by
      simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, decide_eq_true_eq] at hv; exact hv.2,
    by have := bytes_lt σ.mem (State.addr P.nP) P.K; rwa [e.nB] at this⟩) hn0) (VP.seq divB_vp (VP.seq square_vp (VP.seq (minus4n_vp prodF)
    (VP.seq sqrt_vp factors_vp))))

/-- The end of the body: `p`, `q` and the result as `primesKeyDet` gives them. -/
def ResD (P : RP) (σ s : State) : Prop :=
  Bo P σ s ∧ Spec.Rsa.writtenAll s.mem [(State.addr P.pP, P.K), (State.addr P.qP, P.K)] (s.gpr .r0)
    ((Spec.Rsa.primesKeyDet P.nB P.eB (dB P σ)).map fun v => [v.1, v.2])

theorem primesKeyDet_invalid (hv : Spec.Rsa.modulusValid P.n P.K = false) {σ : State} (pre : In P σ) :
    Spec.Rsa.primesKeyDet P.nB P.eB (dB P σ) = none := by
  have hl : P.nB.length = P.K := by rw [← pre.nB]; simp [Spec.Rsa.bytesAt]
  simp only [Spec.Rsa.primesKeyDet, hl, show Spec.Rsa.os2ip P.nB = P.n from rfl, hv, Bool.false_eq_true,
    ite_false]

theorem failD_res {E : State → Prop} (hE : ∀ σ, E σ → Spec.Rsa.primesKeyDet P.nB P.eB (dB P σ) = none)
    {σ s : State}
    (h : E σ ∧ Bo P σ s ∧ Spec.Rsa.bytesAt s.mem (State.addr P.pP) P.K = List.replicate P.K 0 ∧
      Spec.Rsa.bytesAt s.mem (State.addr P.qP) P.K = List.replicate P.K 0 ∧ s.gpr .r0 = 0) : ResD P σ s := by
  obtain ⟨e, h, bp, bq, r0⟩ := h
  refine ⟨h, ?_⟩
  rw [hE σ e]
  refine ⟨r0, fun o ho => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact bp
  · exact bq

theorem feD_res (hv : Spec.Rsa.modulusValid P.n P.K = true) (he : P.el ≤ 8) {σ s : State}
    (h : FeD P (In P) (pF' P) (qF' P) (okF' P) σ s) : ResD P σ s := by
  obtain ⟨pre, bo, bp, bq, ret⟩ := h
  refine ⟨bo, ?_⟩
  rw [pk_eq hv pre he]
  by_cases yes : okF' P σ = true
  · simp only [okF'] at yes
    simp only [yes, ite_true, Option.map_some]
    refine ⟨by rw [ret]; simp only [okF', yes, b2n]; rfl, ?_⟩
    simp only [List.map_cons, List.map_nil, bp, bq, outPD, outQD, okF', yes, ite_true]
  · have no : okV P (fS P) (gS P) σ = false := Bool.eq_false_iff.mpr yes
    simp only [no, Bool.false_eq_true, ite_false, Option.map_none]
    refine ⟨by rw [ret]; simp only [okF', no, b2n]; rfl, fun o ho => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · rw [bp]; simp [outPD, okF', no]
    · rw [bq]; simp [outQD, okF', no]

/-- The body after the entry: Z iff `n` is valid. -/
theorem bodyD_vp [InvLaw] (he : P.el ≤ 8) :
    VP (fun σ s => Bs P σ s ∧ s.z = Spec.Rsa.modulusValid P.n P.K)
      (.ite .eq VG.Impl.Rsa.Arm.RecoverDet.valid VG.Impl.Rsa.Arm.Recover.fail) (ResD P) := by
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) ?_ ?_
  · show some s₁.z = some s₂.z
    rw [h₁.2, h₂.2]
  · refine VP.of_imp (p := Spec.Rsa.modulusValid P.n P.K = true) (fun σ s ⟨⟨_, z⟩, ev⟩ => ?_)
      fun hv => ((validD_vp hv he).mono (fun σ s ⟨⟨h, _⟩, _⟩ => ⟨trivial, h⟩) fun _ _ h => feD_res hv he h)
    have : some s.z = some true := ev
    rw [← z]; simpa using this
  · refine (fail_vp (E := fun σ => In P σ ∧ Spec.Rsa.modulusValid P.n P.K = false)).mono
      (fun σ s ⟨⟨h, z⟩, ev⟩ => ⟨⟨h.pre, ?_⟩, h.bo⟩)
      fun σ s h => failD_res (E := fun σ => In P σ ∧ Spec.Rsa.modulusValid P.n P.K = false)
        (fun σ e => primesKeyDet_invalid e.2 e.1) h
    have : some s.z = some false := ev
    rw [← z]; simpa using this

end

end VG.Proof.Rsa.Arm.RecoverDet
