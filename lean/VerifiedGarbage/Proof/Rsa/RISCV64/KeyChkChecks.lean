module

public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkOps
public import VerifiedGarbage.Proof.Rsa.KeyCheckMath
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! # The checks of an RSA key on RISC-V

As on PPC64LE (`Proof/Rsa/PPC64LE/KcChecks.lean`, `KcMath.lean`): from the
arrays read (`vals`), `start_ok`: `1`, the mask of `p` odd, and the division
of `n` by `p`; `crtChecks_ok`: the checks of `vg_rsa_check_crt_key` and'ed
into the mask (`crtBits`); `dChecks_ok`: those of `d` (`keyBits'`).
`ck_bits`, `cck_bits`: with the products as `mulMod` computes them, the mask
is `keyValid` and `crtKeyValid`.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.KeyCheck

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs setOne bitOf sOdd sB sC)
open VG.Impl.Rsa.RISCV64.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (upd upd_ne upd_self)
open VG.Spec.Rsa (modulusValid exponentValid keyValid crtKeyValid)

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
    (ha : Arrs s0.mem g.B g.w (vals v) live0) (vd : word s0.mem g.B (arr g.w aVD + 8 * g.w) = 0) :
    WP isa (seqs start) s0 fun t => ∃ X₁ X₂, (0 < v.p → X₁ = v.n / v.p ∧ X₂ = v.n % v.p) ∧
      Stg g s0 (aDivN v X₁ X₂) (aVR :: aVQ :: live0) (decide (v.p % 2 = 1)) t := by
  have fit : ∀ j < nArr, arr g.w j + S g.w ≤ 2 ^ 64 := fun j hj => hw.fit64 hj
  rw [start, List.singleton_append, kc_seqs_cons (by simp [divA]), WP.block_append_iff]
  refine WP.mono (setOne_ok hw (j := aOne) (by decide) (by decide)) fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  refine WP.mono (bitOf_ok h1 (j := aP) (sl := sMask) (by decide) (by decide) (by decide) (by decide))
    fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  have o1 : num s0.mem g.B g.w aOne = 0 := by rw [ha.get (by decide)]; rfl
  have p1 : num t1.mem g.B g.w aP = v.p := by
    rw [k1.num (by decide) (by simp) (fit _ (by decide)), ha.get (by decide)]; rfl
  have hl0 : ∀ j ∈ live0, j < nArr := by decide
  have g2 : Stg g s0 (upd (vals v) aOne 1) live0 (decide (v.p % 2 = 1)) t2 := by
    refine ⟨h2, ?_, (r1.trans r2).mono (by decide), ?_, hl0, ?_, ?_⟩
    · exact k1.join k2 (fun j hj => by rw [List.mem_singleton.mp hj]; decide) (by simp) (by simp) (by decide)
    · intro j hj
      by_cases e : j = aOne
      · subst e
        rw [upd_self, k2.num (by simp) (by simp; decide) (fit _ (by decide)), e1, o1]
      · have hjn : j < nArr := hl0 j hj
        rw [upd_ne _ _ e, k2.num (by simp) (by simp; decide) (fit _ hjn),
          k1.num (fun k hk ek => e (by rw [List.mem_singleton.mp hk] at ek; exact ek.symm)) (by simp)
            (fit _ hjn), ha.get hj]
    · rw [k2.word (by omega) (by simp) (by simp; decide) (fit _ (by decide)),
        k1.word (by omega) (by simp; decide) (by simp) (fit _ (by decide)), vd]
    · rw [e2, p1]; exact mask_mod2 v.p
  refine WP.mono (g2.divA_ok (a := aN) (d := aP) (by decide) (by decide) (by decide))
    fun t ⟨Xq, Xr, hv, ht⟩ => ⟨Xq, Xr, fun hp => ?_, ht⟩
  have e := hv (by simp only [upd_ne _ _ (show aP ≠ aOne by decide)]; exact hp)
  simp only [upd_ne _ _ (show aP ≠ aOne by decide), upd_ne _ _ (show aN ≠ aOne by decide)] at e
  exact ⟨e.2, e.1⟩

/-- The checks of `vg_rsa_check_crt_key`. -/
theorem crtChecks_ok {g : Geo} {s0 s : State} {v : Vals} {X₁ X₂ : Nat}
    (h : Stg g s0 (aDivN v X₁ X₂) (aVR :: aVQ :: live0) (decide (v.p % 2 = 1)) s)
    (hq : ∃ a, 1 ≤ a ∧ a < 2 ^ 61 ∧ v.q < 2 ^ (8 * a) ∧ s0.gpr .s6 = BitVec.ofNat 64 a) :
    WP isa (seqs crtChecks) s fun t => ∃ R₁ R₂ R₃ : Nat,
      (v.dP < 2 * (v.p / 2) → 2 * (2 * (v.p / 2)) ≤ 2 ^ (64 * g.w) →
        R₁ = v.e % 2 ^ 33 * v.dP % (2 * (v.p / 2))) ∧
      (v.dQ < 2 * (v.q / 2) → 2 * (2 * (v.q / 2)) ≤ 2 ^ (64 * g.w) →
        R₂ = v.e % 2 ^ 33 * v.dQ % (2 * (v.q / 2))) ∧
      (v.qI < v.p → 2 * v.p ≤ 2 ^ (64 * g.w) → R₃ = v.q * v.qI % v.p) ∧
      Stg g s0 (aFin v) liveFin
        (VG.Proof.Rsa.crtBits v.p v.q v.dP v.dQ v.qI X₁ X₂ R₁ R₂ R₃) t := by
  obtain ⟨qa, qa1, qa2, qlt, q6⟩ := hq
  unfold crtChecks
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [kc_seqs_append (by simp [eqA]) (by simp [eqA])]
  refine WP.mono (h.eqA_ok (a := aVQ) (b := aQ) (by decide) (by decide)) fun t1 h1 => ?_
  rw [kc_seqs_append (by simp [eqA]) (by simp)]
  refine WP.mono (h1.eqA_ok (a := aVR) (b := aZ) (by decide) (by decide)) fun t2 h2 => ?_
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (h2.copy_ok (o := aM1) (a := aP) (by decide) (by decide) (by decide)) fun t3 h3 => ?_
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (h3.clrLow_ok (j := aM1) (by decide) (by decide)) fun t4 h4 => ?_
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (h4.copy_ok (o := aM2) (a := aQ) (by decide) (by decide) (by decide)) fun t5 h5 => ?_
  rw [kc_seqs_cons (by simp [ltA])]
  refine WP.mono (h5.clrLow_ok (j := aM2) (by decide) (by decide)) fun t6 h6 => ?_
  -- `dP`.
  rw [kc_seqs_append (by simp [ltA]) (by simp [mulA])]
  refine WP.mono (h6.ltA_ok (a := aDP) (b := aM1) (by decide) (by decide) (by decide)) fun t7 h7 => ?_
  rw [kc_seqs_append (by simp [mulA]) (by simp [eqA])]
  refine WP.mono (h7.mulA_ok (y := aE) (x := aDP) (m := aM1) (k := 33) (by decide) (by decide) (by decide)
    (by decide) rfl mulIdx_m1 (by decide) (by decide) (by decide) (by decide) fun u _ => cnt33_ok u)
    fun t8 ⟨R₁, hR₁, h8⟩ => ?_
  rw [kc_seqs_append (by simp [eqA]) (by simp [ltA])]
  refine WP.mono (h8.eqA_ok (a := aA) (b := aOne) (by decide) (by decide)) fun t9 h9 => ?_
  -- `dQ`.
  rw [kc_seqs_append (by simp [ltA]) (by simp [mulA])]
  refine WP.mono (h9.ltA_ok (a := aDQ) (b := aM2) (by decide) (by decide) (by decide)) fun t10 h10 => ?_
  rw [kc_seqs_append (by simp [mulA]) (by simp [eqA])]
  refine WP.mono (h10.mulA_ok (y := aE) (x := aDQ) (m := aM2) (k := 33) (by decide) (by decide) (by decide)
    (by decide) rfl mulIdx_m2 (by decide) (by decide) (by decide) (by decide) fun u _ => cnt33_ok u)
    fun t11 ⟨R₂, hR₂, h11⟩ => ?_
  rw [kc_seqs_append (by simp [eqA]) (by simp [ltA])]
  refine WP.mono (h11.eqA_ok (a := aA) (b := aOne) (by decide) (by decide)) fun t12 h12 => ?_
  -- `qInv`.
  rw [kc_seqs_append (by simp [ltA]) (by simp [mulA])]
  refine WP.mono (h12.ltA_ok (a := aQI) (b := aP) (by decide) (by decide) (by decide)) fun t13 h13 => ?_
  rw [kc_seqs_append (by simp [mulA]) (by simp [eqA])]
  refine WP.mono (h13.mulA_ok (y := aQ) (x := aQI) (m := aP) (k := 8 * qa) (by decide) (by decide)
    (by decide) (by decide) rfl mulIdx_p (by decide) (by decide) (by omega) (by omega)
    fun u K => cntQ_ok ((K.gpr (by decide)).trans q6))
    fun t14 ⟨R₃, hR₃, h14⟩ => ?_
  refine WP.mono (h14.eqA_ok (a := aA) (b := aOne) (by decide) (by decide)) fun t h15 => ?_
  refine ⟨R₁, R₂, R₃, hR₁, hR₂, fun hlt hM => ?_, (h15.sub (live' := liveFin) (by decide)).congr' fun j hj => by
    simp only [liveFin, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl⟩
  refine (hR₃ hlt hM).trans ?_
  show v.q % 2 ^ (8 * qa) * v.qI % v.p = _
  rw [Nat.mod_eq_of_lt qlt]

/-- The checks of `d`: `d < n`, and its remainders modulo `p - 1` and `q - 1`
compared with `dP` and `dQ`. -/
theorem dChecks_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : Stg g s0 (aFin v) liveFin c s) :
    WP isa (seqs dChecks) s fun t => ∃ Y₁ Y₂,
      (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2))) ∧ (0 < 2 * (v.q / 2) → Y₂ = v.d % (2 * (v.q / 2))) ∧
      ∃ A live, Stg g s0 A live (c && decide (v.d < v.n) && decide (Y₁ = v.dP) && decide (Y₂ = v.dQ)) t := by
  unfold dChecks
  simp only [List.append_assoc]
  rw [kc_seqs_append (by simp [ltA]) (by simp [divA])]
  refine WP.mono (h.ltA_ok (a := aD) (b := aN) (by decide) (by decide) (by decide)) fun t1 h1 => ?_
  rw [show aFin v aD = v.d from rfl, show aFin v aN = v.n from rfl] at h1
  rw [kc_seqs_append (by simp [divA]) (by simp [eqA])]
  refine WP.mono (h1.divA_ok (a := aD) (d := aM1) (by decide) (by decide) (by decide))
    fun t2 ⟨Xq, Y₁, hv1, h2⟩ => ?_
  rw [show aFin v aD = v.d from rfl, show aFin v aM1 = 2 * (v.p / 2) from rfl] at hv1
  rw [kc_seqs_append (by simp [eqA]) (by simp [divA])]
  refine WP.mono (h2.eqA_ok (a := aVR) (b := aDP) (by decide) (by decide)) fun t3 h3 => ?_
  have h3' : Stg g s0 (aFin v) liveFin (c && decide (v.d < v.n) && decide (Y₁ = v.dP)) t3 := by
    have e : upd (upd (aFin v) aVQ Xq) aVR Y₁ aVR = Y₁ := by rw [upd_self]
    have e2 : upd (upd (aFin v) aVQ Xq) aVR Y₁ aDP = v.dP := rfl
    rw [e, e2] at h3
    exact (h3.sub (live' := liveFin) (by decide)).congr' fun j hj => by
      simp only [liveFin, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [kc_seqs_append (by simp [divA]) (by simp [eqA])]
  refine WP.mono (h3'.divA_ok (a := aD) (d := aM2) (by decide) (by decide) (by decide))
    fun t4 ⟨Xq', Y₂, hv2, h4⟩ => ?_
  rw [show aFin v aD = v.d from rfl, show aFin v aM2 = 2 * (v.q / 2) from rfl] at hv2
  refine WP.mono (h4.eqA_ok (a := aVR) (b := aDQ) (by decide) (by decide)) fun t h5 => ?_
  have e : upd (upd (aFin v) aVQ Xq') aVR Y₂ aVR = Y₂ := by rw [upd_self]
  have e2 : upd (upd (aFin v) aVQ Xq') aVR Y₂ aDQ = v.dQ := rfl
  rw [e, e2] at h5
  exact ⟨Y₁, Y₂, fun hp => (hv1 hp).1, fun hq => (hv2 hq).1, _, _, h5⟩

/-! ## The mask is the spec's -/

theorem fit_two {k w p : Nat} (hk : 1 ≤ k) (hw : 256 ^ k ≤ 2 ^ (64 * w)) (hp : p < 256 ^ (k - 1)) :
    2 * p ≤ 2 ^ (64 * w) := by
  have : 256 ^ k = 256 * 256 ^ (k - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  omega

theorem ck_bits {k n e d p q dP dQ qI w : Nat} (hm : modulusValid n k = true) (he : exponentValid e = true)
    (hp : p < 256 ^ (k - 1)) (hq : q < 256 ^ (k - 1)) (hk : 1 ≤ k) (hw : 256 ^ k ≤ 2 ^ (64 * w))
    {X₁ X₂ R₁ R₂ R₃ Y₁ Y₂ : Nat} (hX : 0 < p → X₁ = n / p ∧ X₂ = n % p)
    (hR₁ : dP < 2 * (p / 2) → 2 * (2 * (p / 2)) ≤ 2 ^ (64 * w) → R₁ = e % 2 ^ 33 * dP % (2 * (p / 2)))
    (hR₂ : dQ < 2 * (q / 2) → 2 * (2 * (q / 2)) ≤ 2 ^ (64 * w) → R₂ = e % 2 ^ 33 * dQ % (2 * (q / 2)))
    (hR₃ : qI < p → 2 * p ≤ 2 ^ (64 * w) → R₃ = q * qI % p)
    (hY₁ : 0 < 2 * (p / 2) → Y₁ = d % (2 * (p / 2))) (hY₂ : 0 < 2 * (q / 2) → Y₂ = d % (2 * (q / 2))) :
    keyValid k n e d p q dP dQ qI = VG.Proof.Rsa.keyBits' n d p q dP dQ qI X₁ X₂ R₁ R₂ R₃ Y₁ Y₂ := by
  have he' : e < 2 ^ 33 := by
    simp only [exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he; exact he.2
  have fp := fit_two hk hw hp
  have fq := fit_two hk hw hq
  refine VG.Proof.Rsa.keyValid_bits hm he hp hq hX (fun h => ?_) (fun h => ?_) (fun h => ?_) hY₁ hY₂
  · rw [hR₁ h (Nat.le_trans (by omega : 2 * (2 * (p / 2)) ≤ 2 * p) fp), Nat.mod_eq_of_lt he']
  · rw [hR₂ h (Nat.le_trans (by omega : 2 * (2 * (q / 2)) ≤ 2 * q) fq), Nat.mod_eq_of_lt he']
  · rw [hR₃ h fp]

theorem cck_bits {k n e p q dP dQ qI w : Nat} (hm : modulusValid n k = true) (he : exponentValid e = true)
    (hp : p < 256 ^ (k - 1)) (hq : q < 256 ^ (k - 1)) (hk : 1 ≤ k) (hw : 256 ^ k ≤ 2 ^ (64 * w))
    {X₁ X₂ R₁ R₂ R₃ : Nat} (hX : 0 < p → X₁ = n / p ∧ X₂ = n % p)
    (hR₁ : dP < 2 * (p / 2) → 2 * (2 * (p / 2)) ≤ 2 ^ (64 * w) → R₁ = e % 2 ^ 33 * dP % (2 * (p / 2)))
    (hR₂ : dQ < 2 * (q / 2) → 2 * (2 * (q / 2)) ≤ 2 ^ (64 * w) → R₂ = e % 2 ^ 33 * dQ % (2 * (q / 2)))
    (hR₃ : qI < p → 2 * p ≤ 2 ^ (64 * w) → R₃ = q * qI % p) :
    crtKeyValid k n e p q dP dQ qI = VG.Proof.Rsa.crtBits p q dP dQ qI X₁ X₂ R₁ R₂ R₃ := by
  have he' : e < 2 ^ 33 := by
    simp only [exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he; exact he.2
  have fp := fit_two hk hw hp
  have fq := fit_two hk hw hq
  refine VG.Proof.Rsa.crtKeyValid_bits hm he hp hq hX (fun h => ?_) (fun h => ?_) (fun h => ?_)
  · rw [hR₁ h (Nat.le_trans (by omega : 2 * (2 * (p / 2)) ≤ 2 * p) fp), Nat.mod_eq_of_lt he']
  · rw [hR₂ h (Nat.le_trans (by omega : 2 * (2 * (q / 2)) ≤ 2 * q) fq), Nat.mod_eq_of_lt he']
  · rw [hR₃ h fp]

/-- A number of `l < k` bytes is below `256^(k - 1)`. -/
theorem lt_pow_of_len (bs : List VG.Byte) {k : Nat} (h : bs.length < k) : Spec.Rsa.os2ip bs < 256 ^ (k - 1) :=
  Nat.lt_of_lt_of_le (VG.Proof.Rsa.lt_of_os2ip bs) (Nat.pow_le_pow_right (by decide) (by omega))

/-- A number of `a` bytes is below `2^(8 a)`. -/
theorem lt_pow8_of_len (bs : List VG.Byte) {a : Nat} (h : bs.length = a) : Spec.Rsa.os2ip bs < 2 ^ (8 * a) := by
  rw [Nat.pow_mul, ← h]; exact VG.Proof.Rsa.lt_of_os2ip bs

/-- `2^(64 w)` for `w = ⌈k / 8⌉` is at least `256^k`. -/
theorem pow_kw (k : Nat) : 256 ^ k ≤ 2 ^ (64 * ((k + 7) / 8)) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by omega)

end VG.Proof.Rsa.RISCV64.KeyCheck
