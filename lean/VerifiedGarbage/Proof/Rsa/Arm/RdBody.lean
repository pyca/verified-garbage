module
-- separate module: the proof of Appendix C.2's body is split in a chain of modules, so that a change rebuilds only the modules after it
public import VerifiedGarbage.Proof.Rsa.Arm.RdSqrt
public import VerifiedGarbage.Proof.Rsa.Arm.RdStore
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel

import VerifiedGarbage.Proof.Rsa.Arm.RvNumbers
import VerifiedGarbage.Proof.Rsa.Arm.RvProd
import VerifiedGarbage.Proof.Rsa.Arm.RvFail
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # `vg_rsa_recover_primes_det` on ARMv7: the body (`bodyD_vp`)

The stages with Appendix C.2's model's steps (`twoStep`, `prodStep`,
`sqrtStep`, `Proof/Rsa/RecoverDet.lean`), whose result is the model's
(`result`), hence `recoverDet`'s (`model_correct`); the factors written out
under the mask (`ResD`). The only module of this port that imports the model.
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
abbrev hS (P : RP) : Nat × Nat × Nat → Nat × Nat × Nat := sqrtStep (32 * P.w) (32 * P.W)

theorem twoF : TwoF P (fS P) := fun _ _ _ => rfl
theorem prodF : ProdF P (gS P) := fun _ _ _ => rfl
theorem sqrtF : SqrtF P (hS P) := fun _ _ _ => rfl

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

theorem okV_result {σ : State} :
    VG.Proof.Rsa.RecoverDet.result (32 * P.w) (32 * P.W) P.n (Mv P σ) (qV P (fS P) (gS P) σ) (remV P (fS P) (gS P) σ) =
      if okV P (fS P) (gS P) (hS P) σ then some (pV P (fS P) (gS P) (hS P) σ, qV' P (fS P) (gS P) (hS P) σ)
      else none := by
  have w1 : 1 < 2 ^ (32 * P.w) := Nat.one_lt_two_pow (by simp only [RP.w]; omega)
  have ql : qV P (fS P) (gS P) σ < 2 ^ (32 * P.w) :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (Nat.two_pow_pos _))
  have hb : bV P (fS P) (gS P) σ = (qV P (fS P) (gS P) σ + 1) % 2 ^ (32 * P.w) := sub32_neg ql w1
  simp only [VG.Proof.Rsa.RecoverDet.result, VG.Proof.Rsa.RecoverDet.stage2, VG.Proof.Rsa.RecoverDet.bOf, VG.Proof.Rsa.RecoverDet.rootOf, VG.Proof.Rsa.RecoverDet.ok4Of,
    VG.Proof.Rsa.RecoverDet.xOf, VG.Proof.Rsa.RecoverDet.sqOf, VG.Proof.Rsa.RecoverDet.fourN, VG.Proof.Rsa.RecoverDet.ltOf, VG.Proof.Rsa.RecoverDet.mOf, VG.Proof.Rsa.RecoverDet.okDE,
    VG.Proof.Rsa.RecoverDet.deX]
  simp only [← aV_eq, ← hb, show 32 * P.W / 2 = 16 * P.W by omega, okV, Bool.and_assoc]
  rfl

theorem pow_le_w {k : Nat} (hk : k ≤ 8 * P.K + 64) : 2 ^ k ≤ 2 ^ (32 * P.w) :=
  Nat.pow_le_pow_right (by decide) (by simp only [RP.w, RP.w6]; omega)

theorem rd_eq (hv : Spec.Rsa.modulusValid P.n P.K = true) {σ : State} (pre : In P σ) (he : P.el ≤ 8) :
    Spec.Rsa.recoverDet P.n P.e (dv P σ) =
      if okV P (fS P) (gS P) (hS P) σ then some (pV P (fS P) (gS P) (hS P) σ, qV' P (fS P) (gS P) (hS P) σ)
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
  rw [← VG.Proof.Rsa.RecoverDet.model_correct (nb := 32 * P.w) (wb := 32 * P.W)
    (q := qV P (fS P) (gS P) σ) (rem := remV P (fS P) (gS P) σ) odd three hn hde (by simp only [RP.W]; omega)
    (by omega) fun pos => ?_]
  · exact okV_result
  have hm : VG.Proof.Rsa.RecoverDet.m1Of (32 * P.w) (32 * P.W) P.n (dv P σ * P.e) = m1R P (fS P) (gS P) σ := by
    rw [m1R, sub32_neg (Nat.mod_lt _ (Nat.two_pow_pos _)) w1, VG.Proof.Rsa.RecoverDet.m1Of,
      VG.Proof.Rsa.RecoverDet.mOf, ← aV_eq]
  have hd : VG.Proof.Rsa.RecoverDet.dOf (32 * P.w) (32 * P.W) P.n (dv P σ * P.e) = dV P (fS P) (gS P) σ := by
    rw [VG.Proof.Rsa.RecoverDet.dOf, VG.Proof.Rsa.RecoverDet.rOf, ← aV_eq]; rfl
  rw [hm] at pos ⊢
  rw [hd]
  have : m1V P (fS P) (gS P) σ = m1R P (fS P) (gS P) σ := by simp only [m1V]; split <;> omega
  exact ⟨by rw [← this], by rw [← this]⟩

theorem pk_eq (hv : Spec.Rsa.modulusValid P.n P.K = true) {σ : State} (pre : In P σ) (he : P.el ≤ 8) :
    Spec.Rsa.primesKeyDet P.nB P.eB (dB P σ) =
      if okV P (fS P) (gS P) (hS P) σ then
        some (Spec.Rsa.i2osp (pV P (fS P) (gS P) (hS P) σ) P.K, Spec.Rsa.i2osp (qV' P (fS P) (gS P) (hS P) σ) P.K)
      else none := by
  have hl : P.nB.length = P.K := by rw [← pre.nB]; simp [Spec.Rsa.bytesAt]
  simp only [Spec.Rsa.primesKeyDet, hl, show Spec.Rsa.os2ip P.nB = P.n from rfl, hv, ite_true]
  rw [show Spec.Rsa.os2ip P.eB = P.e from rfl, show Spec.Rsa.os2ip (dB P σ) = dv P σ from rfl, rd_eq hv pre he]
  cases okV P (fS P) (gS P) (hS P) σ <;> rfl

theorem factors_lt (hv : Spec.Rsa.modulusValid P.n P.K = true) {σ : State} (pre : In P σ) (he : P.el ≤ 8)
    (ok : okV P (fS P) (gS P) (hS P) σ = true) :
    pV P (fS P) (gS P) (hS P) σ < 2 ^ (8 * P.K) ∧ qV' P (fS P) (gS P) (hS P) σ < 2 ^ (8 * P.K) := by
  have e := rd_eq hv pre he
  simp only [ok, ↓reduceIte] at e
  have m := VG.Proof.Rsa.RecoverDet.recoverDet_mul e
  have nK : P.n < 2 ^ (8 * P.K) := by have := bytes_lt σ.mem (State.addr P.nP) P.K; rwa [pre.nB] at this
  obtain ⟨odd, three⟩ := valid_facts' hv (by have := pre.k1; omega)
  have p0 : 0 < pV P (fS P) (gS P) (hS P) σ := Nat.pos_of_ne_zero fun h => by rw [h] at m; omega
  have q0 : 0 < qV' P (fS P) (gS P) (hS P) σ := Nat.pos_of_ne_zero fun h => by rw [h] at m; omega
  constructor
  · exact Nat.lt_of_le_of_lt (by rw [← m]; exact Nat.le_mul_of_pos_right _ q0) nK
  · exact Nat.lt_of_le_of_lt (by rw [← m]; exact Nat.le_mul_of_pos_left _ p0) nK

theorem pcfgA : PCfg aG wX3 wA wT1 wT2 wZ LG LWT [sOkDE] := by
  constructor <;> decide

/-- The factors and the mask. -/
abbrev pF' (P : RP) : State → Nat := pV P (fS P) (gS P) (hS P)
abbrev qF' (P : RP) : State → Nat := qV' P (fS P) (gS P) (hS P)
abbrev okF' (P : RP) : State → Bool := okV P (fS P) (gS P) (hS P)

theorem validD_vp [InvLaw] (hv : Spec.Rsa.modulusValid P.n P.K = true) (he : P.el ≤ 8) :
    VP (fun σ s => True ∧ Bs P σ s) VG.Impl.Rsa.Arm.RecoverDet.valid (FeD P (In P) (pF' P) (qF' P) (okF' P)) := by
  have hn0 : 0 < P.n := by
    simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv; omega
  simp only [VG.Impl.Rsa.Arm.RecoverDet.valid, seqs]
  refine (loads_vp (E := In P)).mono (fun σ s ⟨_, h⟩ => ⟨h.pre, h⟩) (fun _ _ h => h) |>.seq ?_
  refine ((prod_vp (E := In P)).mono (fun σ s ⟨e, h⟩ => ⟨e, h.ks⟩) fun _ _ h => h).seq ?_
  refine VP.seq ?_ (storesD_vp (pF' P) (qF' P) (okF' P) (fun σ e ok => (factors_lt hv e he ok).1)
    (fun σ e ok => (factors_lt hv e he ok).2))
  simp only [det, seqs]
  refine VP.seq deMinus_vp (VP.seq (twos_vp twoF) (VP.seq (gcd_vp fun σ e => u_odd hv e) ?_))
  refine VP.seq (product_vp pcfgA prodF (fun σ _ => by simp only [AWG]; rd_up) productPreA_taint
    productStepA_taint) ?_
  refine VP.seq (divA_vp hn0) (VP.seq divB_vp (VP.seq (square_vp prodF) (VP.seq minus4n_vp
    (VP.seq (sqrt_vp sqrtF) factors_vp))))

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
  · have no : okV P (fS P) (gS P) (hS P) σ = false := Bool.eq_false_iff.mpr yes
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
