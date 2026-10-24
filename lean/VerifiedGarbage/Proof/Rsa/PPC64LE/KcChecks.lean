module

import VerifiedGarbage.Proof.Rsa.PPC64LE.KcOps
public import VerifiedGarbage.Proof.Rsa.KeyCheckMath
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcBase
public import VerifiedGarbage.Proof.Rsa.PPC64LE.MulMod

/-! # The checks of an RSA key on PPC64LE

As on ARMv7 (`Proof/Rsa/Arm/KcStart.lean`, `KcChecks.lean`, `KcBody.lean`):
from the arrays read (`vals`), `start_ok`: `1`, the mask of `p` odd, and the
division of `n` by `p`; `crtChecks_ok`: the checks of `vg_rsa_check_crt_key`
and'ed into the mask (`crtBits`); `dChecks_ok`: those of `d` (`keyBits'`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs setOne bitOf sOdd sB sC)
open VG.Impl.Rsa.PPC64LE.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (arr S num slot Arrs upd upd_ne upd_self)

/-- The arrays the checks start from. -/
abbrev live0 : List Nat := [aZ, aOne, aN, aE, aP, aQ, aDP, aDQ, aQI, aD]

/-- The arrays after the division of `n` by `p`. -/
abbrev aDivN (v : Vals) (X₁ X₂ : Nat) : Nat → Nat := upd (upd (upd (vals v) aOne 1) aVQ X₁) aVR X₂

/-- The arrays the checks of `d` use. -/
abbrev aFin (v : Vals) : Nat → Nat := upd (upd (vals v) aM1 (2 * (v.p / 2))) aM2 (2 * (v.q / 2))
abbrev liveFin : List Nat := [aZ, aN, aD, aDP, aDQ, aM1, aM2]

theorem mulIdx_m1 : MulIdx nArr aZ aY aX aA aM1 aT := by decide
theorem mulIdx_m2 : MulIdx nArr aZ aY aX aA aM2 aT := by decide
theorem mulIdx_p : MulIdx nArr aZ aY aX aA aP aT := by decide

theorem mask_mod2 (x : Nat) : x % 2 = if decide (x % 2 = 1) then 1 else 0 := by
  rcases Nat.mod_two_eq_zero_or_one x with e | e <;> simp [e]

/-- `start`: `1`, the mask of `p` odd, and `n / p` and `n mod p`. -/
theorem start_ok {g : Geo} {s0 : State} {v : Vals} (hw : Ws s0 g.B g.Z g.w nArr)
    (ha : Arrs s0.mem g.B g.w (vals v) live0) (vd : w32 s0.mem g.B (arr g.w aVD + 4 * g.w) = 0) :
    WP isa (seqs start) s0 fun t => ∃ X₁ X₂, (0 < v.p → X₁ = v.n / v.p ∧ X₂ = v.n % v.p) ∧
      Stg g s0 (aDivN v X₁ X₂) (aVR :: aVQ :: live0) (decide (v.p % 2 = 1)) t := by
  have fit : ∀ j < nArr, arr g.w j + S g.w ≤ 2 ^ 64 := fun j hj => hw.fit64 hj
  rw [start, List.singleton_append, wp_seqs_cons (by simp [divA])]
  refine setOne_ok hw (j := aOne) (by decide) (by decide) fun t1 h1 k1 e1 r1 => ?_
  rw [← List.append_nil (bitOf sMask aP)]
  refine bitOf_ok h1 (j := aP) (sl := sMask) (by decide) (by decide) (by decide)
    fun t2 h2 k2 e2 r2 => WP.block_nil ?_
  have o1 : num s0.mem g.B g.w aOne = 0 := by rw [ha.get (by decide)]; rfl
  have p1 : num t1.mem g.B g.w aP = v.p := by
    rw [k1.num (by decide) (by simp) (fit _ (by decide)), ha.get (by decide)]; rfl
  have hl0 : ∀ j ∈ live0, j < nArr := by decide
  have g2 : Stg g s0 (upd (vals v) aOne 1) live0 (decide (v.p % 2 = 1)) t2 := by
    refine ⟨h2, ?_, (r1.trans r2).mono, ?_, ?_, ?_, ?_⟩
    · exact (k1.mono (js' := List.range nArr) (ds' := bodySlots)
        (fun j hj => by rw [List.mem_singleton.mp hj]; decide) (by simp)).trans
        (k2.mono (js' := List.range nArr) (ds' := bodySlots) (by simp) (by decide))
    · intro j hj
      by_cases e : j = aOne
      · subst e
        rw [upd_self, k2.num (by simp) (by simp; decide) (fit _ (by decide)), e1, o1]
      · have hjn : j < nArr := hl0 j hj
        rw [upd_ne _ _ e, k2.num (by simp) (by simp; decide) (fit _ hjn),
          k1.num (fun k hk ek => e (by rw [List.mem_singleton.mp hk] at ek; exact ek.symm)) (by simp)
            (fit _ hjn), ha.get hj]
    · exact hl0
    · rw [k2.word (by simp only [S]; omega) (by simp) (by simp; decide) (fit _ (by decide)),
        k1.word (by simp only [S]; omega) (by simp; decide) (by simp) (fit _ (by decide)), vd]
    · rw [e2, p1]; exact mask_mod2 v.p
  refine WP.mono (g2.divA_ok (a := aN) (d := aP) (by decide) (by decide) (by decide))
    fun t ⟨Xq, Xr, hv, ht⟩ => ⟨Xq, Xr, fun hp => ?_, ht⟩
  have e := hv (by simp only [upd_ne _ _ (show aP ≠ aOne by decide)]; exact hp)
  simp only [upd_ne _ _ (show aP ≠ aOne by decide), upd_ne _ _ (show aN ≠ aOne by decide)] at e
  exact ⟨e.2, e.1⟩

/-- The checks of `vg_rsa_check_crt_key`. -/
theorem crtChecks_ok {g : Geo} {s0 s : State} {v : Vals} {X₁ X₂ : Nat}
    (h : Stg g s0 (aDivN v X₁ X₂) (aVR :: aVQ :: live0) (decide (v.p % 2 = 1)) s) :
    WP isa (seqs crtChecks) s fun t => ∃ R₁ R₂ R₃ : Nat,
      (v.dP < 2 * (v.p / 2) → 2 * (2 * (v.p / 2)) ≤ 2 ^ (32 * g.w) →
        R₁ = v.e % 2 ^ 33 * v.dP % (2 * (v.p / 2))) ∧
      (v.dQ < 2 * (v.q / 2) → 2 * (2 * (v.q / 2)) ≤ 2 ^ (32 * g.w) →
        R₂ = v.e % 2 ^ 33 * v.dQ % (2 * (v.q / 2))) ∧
      (v.qI < v.p → 2 * v.p ≤ 2 ^ (32 * g.w) → R₃ = v.q % 2 ^ (32 * g.w) * v.qI % v.p) ∧
      Stg g s0 (aFin v) liveFin
        (VG.Proof.Rsa.crtBits v.p v.q v.dP v.dQ v.qI X₁ X₂ R₁ R₂ R₃) t := by
  have wpos := h.ws.wpos
  have wle := h.ws.wle
  unfold crtChecks
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [wp_seqs_append (by simp [eqA]) (by simp [eqA])]
  refine WP.mono (h.eqA_ok (a := aVQ) (b := aQ) (by decide) (by decide)) fun t1 h1 => ?_
  rw [wp_seqs_append (by simp [eqA]) (by simp)]
  refine WP.mono (h1.eqA_ok (a := aVR) (b := aZ) (by decide) (by decide)) fun t2 h2 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h2.copy_ok (o := aM1) (a := aP) (by decide) (by decide) (by decide)) fun t3 h3 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h3.clrLow_ok (j := aM1) (by decide)) fun t4 h4 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h4.copy_ok (o := aM2) (a := aQ) (by decide) (by decide) (by decide)) fun t5 h5 => ?_
  rw [wp_seqs_cons (by simp [ltA])]
  refine WP.mono (h5.clrLow_ok (j := aM2) (by decide)) fun t6 h6 => ?_
  -- `dP`.
  rw [wp_seqs_append (by simp [ltA]) (by simp [mulA])]
  refine WP.mono (h6.ltA_ok (a := aDP) (b := aM1) (by decide) (by decide) (by decide)) fun t7 h7 => ?_
  rw [wp_seqs_append (by simp [mulA]) (by simp [eqA])]
  refine WP.mono (h7.mulA_ok (y := aE) (x := aDP) (m := aM1) (k := 33) (by decide) (by decide) (by decide)
    (by decide) rfl mulIdx_m1 (by decide) (by decide) (by decide) (by decide) fun u _ => cnt33_ok u)
    fun t8 ⟨R₁, hR₁, h8⟩ => ?_
  rw [wp_seqs_append (by simp [eqA]) (by simp [ltA])]
  refine WP.mono (h8.eqA_ok (a := aA) (b := aOne) (by decide) (by decide)) fun t9 h9 => ?_
  -- `dQ`.
  rw [wp_seqs_append (by simp [ltA]) (by simp [mulA])]
  refine WP.mono (h9.ltA_ok (a := aDQ) (b := aM2) (by decide) (by decide) (by decide)) fun t10 h10 => ?_
  rw [wp_seqs_append (by simp [mulA]) (by simp [eqA])]
  refine WP.mono (h10.mulA_ok (y := aE) (x := aDQ) (m := aM2) (k := 33) (by decide) (by decide) (by decide)
    (by decide) rfl mulIdx_m2 (by decide) (by decide) (by decide) (by decide) fun u _ => cnt33_ok u)
    fun t11 ⟨R₂, hR₂, h11⟩ => ?_
  rw [wp_seqs_append (by simp [eqA]) (by simp [ltA])]
  refine WP.mono (h11.eqA_ok (a := aA) (b := aOne) (by decide) (by decide)) fun t12 h12 => ?_
  -- `qInv`.
  rw [wp_seqs_append (by simp [ltA]) (by simp [mulA])]
  refine WP.mono (h12.ltA_ok (a := aQI) (b := aP) (by decide) (by decide) (by decide)) fun t13 h13 => ?_
  rw [wp_seqs_append (by simp [mulA]) (by simp [eqA])]
  refine WP.mono (h13.mulA_ok (y := aQ) (x := aQI) (m := aP) (k := 32 * g.w) (by decide) (by decide)
    (by decide) (by decide) rfl mulIdx_p (by decide) (by decide) (by omega) (by omega) fun u hu => cntW_ok hu)
    fun t14 ⟨R₃, hR₃, h14⟩ => ?_
  refine WP.mono (h14.eqA_ok (a := aA) (b := aOne) (by decide) (by decide)) fun t h15 => ?_
  exact ⟨R₁, R₂, R₃, hR₁, hR₂, hR₃, (h15.sub (live' := liveFin) (by decide)).congr' fun j hj => by
    simp only [liveFin, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl⟩

theorem aFin_d (v : Vals) : aFin v aD = v.d := rfl
theorem aFin_n (v : Vals) : aFin v aN = v.n := rfl
theorem aFin_dP (v : Vals) : aFin v aDP = v.dP := rfl
theorem aFin_dQ (v : Vals) : aFin v aDQ = v.dQ := rfl
theorem aFin_m1 (v : Vals) : aFin v aM1 = 2 * (v.p / 2) := rfl
theorem aFin_m2 (v : Vals) : aFin v aM2 = 2 * (v.q / 2) := rfl

/-- The checks of `d`: `d < n`, and its remainders modulo `p - 1` and `q - 1`
compared with `dP` and `dQ`. -/
theorem dChecks_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : Stg g s0 (aFin v) liveFin c s) :
    WP isa (seqs dChecks) s fun t => ∃ Y₁ Y₂,
      (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2))) ∧ (0 < 2 * (v.q / 2) → Y₂ = v.d % (2 * (v.q / 2))) ∧
      ∃ A live, Stg g s0 A live (c && decide (v.d < v.n) && decide (Y₁ = v.dP) && decide (Y₂ = v.dQ)) t := by
  unfold dChecks
  simp only [List.append_assoc]
  rw [wp_seqs_append (by simp [ltA]) (by simp [divA])]
  refine WP.mono (h.ltA_ok (a := aD) (b := aN) (by decide) (by decide) (by decide)) fun t1 h1 => ?_
  rw [aFin_d, aFin_n] at h1
  rw [wp_seqs_append (by simp [divA]) (by simp [eqA])]
  refine WP.mono (h1.divA_ok (a := aD) (d := aM1) (by decide) (by decide) (by decide))
    fun t2 ⟨Xq, Y₁, hv1, h2⟩ => ?_
  rw [aFin_d, aFin_m1] at hv1
  rw [wp_seqs_append (by simp [eqA]) (by simp [divA])]
  refine WP.mono (h2.eqA_ok (a := aVR) (b := aDP) (by decide) (by decide)) fun t3 h3 => ?_
  have h3' : Stg g s0 (aFin v) liveFin (c && decide (v.d < v.n) && decide (Y₁ = v.dP)) t3 := by
    have e : upd (upd (aFin v) aVQ Xq) aVR Y₁ aVR = Y₁ := by rw [upd_self]
    have e2 : upd (upd (aFin v) aVQ Xq) aVR Y₁ aDP = v.dP := rfl
    rw [e, e2] at h3
    exact (h3.sub (live' := liveFin) (by decide)).congr' fun j hj => by
      simp only [liveFin, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [wp_seqs_append (by simp [divA]) (by simp [eqA])]
  refine WP.mono (h3'.divA_ok (a := aD) (d := aM2) (by decide) (by decide) (by decide))
    fun t4 ⟨Xq', Y₂, hv2, h4⟩ => ?_
  rw [aFin_d, aFin_m2] at hv2
  refine WP.mono (h4.eqA_ok (a := aVR) (b := aDQ) (by decide) (by decide)) fun t h5 => ?_
  have e : upd (upd (aFin v) aVQ Xq') aVR Y₂ aVR = Y₂ := by rw [upd_self]
  have e2 : upd (upd (aFin v) aVQ Xq') aVR Y₂ aDQ = v.dQ := rfl
  rw [e, e2] at h5
  exact ⟨Y₁, Y₂, fun hp => (hv1 hp).1, fun hq => (hv2 hq).1, _, _, h5⟩

end VG.Proof.Rsa.PPC64LE.KeyCheck
