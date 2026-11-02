module

public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkPre
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkOps
public import VerifiedGarbage.Proof.Rsa.KeyCheckMath
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Impl.Rsa.RISCV64.CheckKey
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The checks of an RSA key on RISC-V, and `vg_rsa_check_key` correct

As on PPC64LE (`Proof/Rsa/PPC64LE/KcChecks.lean`, `KcMath.lean`, `KcCk.lean`,
`KcCkMain.lean`). The checks: from the arrays read (`vals`), `start_ok`: `1`,
the mask of `p` odd, and the division of `n` by `p`; `crtChecks_ok`: the
checks of `vg_rsa_check_crt_key` and'ed into the mask (`crtBits`);
`dChecks_ok`: those of `d` (`keyBits'`). `ck_bits`, `cck_bits`: with the
products as `mulMod` computes them, the mask is `keyValid` and
`crtKeyValid`.

`vg_rsa_check_key`: `ck_moves_ok`, the arguments into the registers the code
keeps them in (`CkRegs`); `ck_valid`, the valid branch: the arrays set up,
the numbers read, the checks, and the mask returned, which is `checkKey`;
`ck_main`, the function (`fn_ok`); `ck_correct`.
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

namespace VG.Proof.Rsa.RISCV64.KeyCheck

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs saved mov load)
open VG.Impl.Rsa.RISCV64.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (upd upd_ne upd_self)
open VG.Proof.Bignum.RISCV64.Pub (sat)

theorem stackArg_write (s : State) (r : Reg) (v : BitVec 64) (i : Nat) :
    stackArg (s.write r v) i = stackArg s i := rfl

theorem len_bytes (m : Mem) (p : Addr) (L : Nat) : (Spec.Rsa.bytesAt m p L).length = L := by
  simp [Spec.Rsa.bytesAt]

/-- The stack arguments, after `save`. -/
theorem stackArg_saved {s0 u : State} {B : Addr} {Z K oS na : Nat} (hp : KPre s0 B Z K oS na)
    (h : KBase B Z s0 u) (hsp : u.sp = s0.sp) {i : Nat} (hi : i < na) : stackArg u i = stackArg s0 i := by
  have hs := hp.sp
  unfold stackArg
  rw [show stackArgAddr u i = stackArgAddr s0 i by simp only [stackArgAddr, hsp]]
  refine Mem.readW_congr fun b hb => h.frame _ (past_of_disjoint hp.disj.symm ?_)
  rw [stackArgAddr_eq s0 i, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact Offset.contains_base _ (by omega) (by omega)

theorem ofNat_toNat' (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

/-- The pointers and lengths of `vg_rsa_check_key`, kept by the entry. -/
structure CkRegs (s0 t : State) : Prop where
  s1 : t.gpr .s1 = s0.gpr .a0
  s2 : t.gpr .s2 = s0.gpr .a1
  s3 : t.gpr .s3 = s0.gpr .a6
  s4 : t.gpr .s4 = s0.gpr .a7
  a0 : t.gpr .a0 = s0.gpr .a4
  a1 : t.gpr .a1 = s0.gpr .a5
  s5 : t.gpr .s5 = stackArg s0 0
  s6 : t.gpr .s6 = stackArg s0 1
  a2 : t.gpr .a2 = stackArg s0 2
  a3 : t.gpr .a3 = stackArg s0 4
  a6 : t.gpr .a6 = stackArg s0 6

abbrev ckRegs : List Reg := [.s1, .s2, .s3, .s4, .a0, .a1, .s5, .s6, .a2, .a3, .a6]

theorem CkRegs.of_keep {s0 t u : State} (h : CkRegs s0 t) {rs : List Reg} (k : Keep rs t u)
    (hr : ∀ r ∈ ckRegs, r ∉ rs := by decide) : CkRegs s0 u := by
  have e : ∀ r ∈ ckRegs, u.gpr r = t.gpr r := fun r hr' => k.gpr (hr r hr')
  exact ⟨(e _ (by decide)).trans h.s1, (e _ (by decide)).trans h.s2, (e _ (by decide)).trans h.s3,
    (e _ (by decide)).trans h.s4, (e _ (by decide)).trans h.a0, (e _ (by decide)).trans h.a1,
    (e _ (by decide)).trans h.s5, (e _ (by decide)).trans h.s6, (e _ (by decide)).trans h.a2,
    (e _ (by decide)).trans h.a3, (e _ (by decide)).trans h.a6⟩

/-- The arguments into their registers. -/
theorem ck_moves_ok {s0 : State} (h0 : CkP s0) (u : State) (hu : Saved s0 (stackArg s0 8) u) :
    WP isa (.block VG.Impl.Rsa.RISCV64.CheckKey.moves) u fun v => CkRegs s0 v ∧ v.mem = u.mem ∧
      v.rd = u.rd ∧ v.wr = u.wr ∧ v.gpr .s11 = u.gpr .s11 ∧ v.gpr .a4 = off (s0.gpr .a2) 0 ∧
      v.gpr .a5 = BitVec.ofNat 64 (s0.gpr .a3).toNat ∧ v.gpr .s1 = off (s0.gpr .a0) 0 ∧
      v.gpr .s2 = BitVec.ofNat 64 (s0.gpr .a1).toNat := by
  have hp := ck_kpre h0
  have bu := KBase.of_saved (Z := (stackArg s0 9).toNat * 8) hu (by have := hp.zk; omega)
  have g : ∀ r, r ≠ .t0 → r ≠ .s11 → u.gpr r = s0.gpr r := fun r h1 h2 =>
    hu.keep.gpr (by simp [h1, h2])
  have sa : ∀ i < 10, stackArg u i = stackArg s0 i := fun i hi => stackArg_saved hp bu hu.sp hi
  rw [show VG.Impl.Rsa.RISCV64.CheckKey.moves = [mov .s1 .a0, mov .s2 .a1, mov .s3 .a6, mov .s4 .a7,
      mov .a0 .a4, mov .a1 .a5, mov .a4 .a2, mov .a5 .a3, .addSp .t0 0] ++
      [.load .d .s5 .t0 0, .load .d .s6 .t0 8, .load .d .a2 .t0 16, .load .d .a3 .t0 32,
        .load .d .a6 .t0 48] from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.s1, .s2, .s3, .s4, .a0, .a1, .a4, .a5, .t0] (Q := fun x =>
    x.gpr .s1 = u.gpr .a0 ∧ x.gpr .s2 = u.gpr .a1 ∧ x.gpr .s3 = u.gpr .a6 ∧ x.gpr .s4 = u.gpr .a7 ∧
    x.gpr .a0 = u.gpr .a4 ∧ x.gpr .a1 = u.gpr .a5 ∧ x.gpr .a4 = u.gpr .a2 ∧ x.gpr .a5 = u.gpr .a3 ∧
    x.gpr .t0 = u.sp ∧ x.mem = u.mem ∧ x.sp = u.sp) (by
      brun [mov, add_ofNat_zero', exec_addSp (show 0 < 2048 by decide)]) (by rfl) (by rfl))
    fun x ⟨⟨x1, x2, x3, x4, x0', x1', x4', x5', xt, xm, xsp⟩, kx⟩ => ?_
  have sx : ∀ i, stackArg x i = stackArg u i := fun i => by simp only [stackArg, stackArgAddr, xm, xsp]
  have hin : ∀ i < 10, InRegions (x.rd ++ x.wr) (stackArgAddr x i) 8 := fun i hi => by
    rw [kx.2.1, kx.2.2, hu.keep.2.1, hu.keep.2.2, show stackArgAddr x i = stackArgAddr s0 i by
      simp only [stackArgAddr, xsp, hu.sp]]
    exact hp.arg_rd hi
  have hal : ∀ i < 10, (stackArgAddr x i).toNat % 8 = 0 := fun i hi => by
    rw [show stackArgAddr x i = stackArgAddr s0 i by simp only [stackArgAddr, xsp, hu.sp]]
    exact hp.arg_al hi
  have t0w : ∀ (y : State) (r : Reg) (a : BitVec 64), r ≠ .t0 → y.gpr .t0 = y.sp →
      (y.write r a).gpr .t0 = (y.write r a).sp := fun y r a hr hy => by
    rw [gpr_write_of_ne _ _ (Ne.symm hr)]; exact hy
  have x0 : x.gpr .t0 = x.sp := by rw [xt, xsp]
  let y1 := x.write .s5 (stackArg x 0)
  let y2 := y1.write .s6 (stackArg y1 1)
  let y3 := y2.write .a2 (stackArg y2 2)
  let y4 := y3.write .a3 (stackArg y3 4)
  have e0 := x0
  have e1 : y1.gpr .t0 = y1.sp := t0w _ _ _ (by decide) e0
  have e2 : y2.gpr .t0 = y2.sp := t0w _ _ _ (by decide) e1
  have e3 : y3.gpr .t0 = y3.sp := t0w _ _ _ (by decide) e2
  have e4 : y4.gpr .t0 = y4.sp := t0w _ _ _ (by decide) e3
  refine ldSp_ok (u := x) e0 (i := 0) rfl (by decide) (hin 0 (by decide)) (hal 0 (by decide)) ?_
  refine ldSp_ok (u := y1) e1 (i := 1) rfl (by decide) (hin 1 (by decide)) (hal 1 (by decide)) ?_
  refine ldSp_ok (u := y2) e2 (i := 2) rfl (by decide) (hin 2 (by decide)) (hal 2 (by decide)) ?_
  refine ldSp_ok (u := y3) e3 (i := 4) rfl (by decide) (hin 4 (by decide)) (hal 4 (by decide)) ?_
  refine ldSp_ok (u := y4) e4 (i := 6) rfl (by decide) (hin 6 (by decide)) (hal 6 (by decide)) ?_
  refine WP.block_nil ?_
  simp only [y1, y2, y3, y4, stackArg_write, sx, sa _ (by decide : 0 < 10), sa _ (by decide : 1 < 10), sa _ (by decide : 2 < 10),
    sa _ (by decide : 4 < 10), sa _ (by decide : 6 < 10)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, xm, kx.2.1, kx.2.2, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [gpr_write, reduceCtorEq, x1, x2, x3, x4, x0', x1', x4', x5',
      g .a0 (by decide) (by decide), g .a1 (by decide) (by decide), g .a2 (by decide) (by decide),
      g .a3 (by decide) (by decide), g .a4 (by decide) (by decide), g .a5 (by decide) (by decide),
      g .a6 (by decide) (by decide), g .a7 (by decide) (by decide), ↓reduceIte,
      kx.gpr (r := .s11) (by decide), add_ofNat_zero', BitVec.ofNat_toNat, BitVec.setWidth_eq] <;> rfl

/-- `checkKey` of the arguments. -/
abbrev ckOk (s0 : State) : Bool :=
  Spec.Rsa.checkKey (Spec.Rsa.bytesAt s0.mem (s0.gpr .a0) (s0.gpr .a1).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .a2) (s0.gpr .a3).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .a4) (s0.gpr .a5).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .a6) (s0.gpr .a7).toNat)
    (Spec.Rsa.bytesAt s0.mem (stackArg s0 0) (stackArg s0 1).toNat)
    (Spec.Rsa.bytesAt s0.mem (stackArg s0 2) (s0.gpr .a7).toNat)
    (Spec.Rsa.bytesAt s0.mem (stackArg s0 4) (stackArg s0 1).toNat)
    (Spec.Rsa.bytesAt s0.mem (stackArg s0 6) (s0.gpr .a7).toNat)

theorem ck_valid {s0 t : State} (h0 : CkP s0)
    (hb : KBase (stackArg s0 8) ((stackArg s0 9).toNat * 8) s0 t) (hr : CkRegs s0 t)
    (h4 : t.gpr .a4 = BitVec.ofNat 64
      (sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a2) (s0.gpr .a3).toNat))) <<< 31)
    (hev : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a2) (s0.gpr .a3).toNat))
      = true)
    (hmv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a0) (s0.gpr .a1).toNat))
      (s0.gpr .a1).toNat = true) :
    WP isa (seqs (([setup, .block eArr] : List (Prog isa)) ++ VG.Impl.Rsa.RISCV64.CheckKey.loads ++
        (start ++ crtChecks ++ dChecks) ++ ([.block ret] : List (Prog isa)))) t fun u =>
      KBase (stackArg s0 8) ((stackArg s0 9).toNat * 8) s0 u ∧
        u.gpr .a0 = BitVec.ofNat 64 (if ckOk s0 then 1 else 0) := by
  have hp := ck_kpre h0
  obtain ⟨-, hw8, -, hkw⟩ := hp.ws
  have he' : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a2) (s0.gpr .a3).toNat) < 2 ^ 33 := by
    simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hev; exact hev.2
  have hsat : sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a2) (s0.gpr .a3).toNat)) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a2) (s0.gpr .a3).toNat) := by
    unfold sat; omega
  rw [hsat] at h4
  have p1 := h0.p1; have p2 := h0.p2; have q1 := h0.q1; have q2 := h0.q2
  have d1 := h0.d1; have d2 := h0.d2
  have k1024 := hp.k1024
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (WP.keep [.s9, .s10, .t0, .t3, .t5] (setup_ok hp hb (hr.s2.trans (ofNat_toNat' _)))
    (by rfl) (by rfl)) fun t1 ⟨⟨b1, w1, z1, _⟩, k1⟩ => ?_
  rw [kc_seqs_cons (by simp [VG.Impl.Rsa.RISCV64.CheckKey.loads])]
  refine WP.mono (eArr_ok (LdS.of_setup b1 w1 z1) rfl (by rw [k1.gpr (by decide)]; exact h4) he')
    fun t2 ⟨l2, k2⟩ => ?_
  have R := (hr.of_keep k1).of_keep k2
  simp only [VG.Impl.Rsa.RISCV64.CheckKey.loads, List.cons_append]
  -- `n`.
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (ldStep_ok l2 (j := aN) (by decide) rfl (by decide) R.s1 (R.s2.trans (ofNat_toNat' _))
    (by have := hp.k64; omega) (by omega) (by rw [h0.hrd]; simp) h0.dn h0.wn) fun t3 ⟨l3, k3⟩ => ?_
  have R3 := R.of_keep k3
  -- `d`.
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (ldStep_ok l3 (j := aD) (by decide) rfl (by decide) R3.a0 (R3.a1.trans (ofNat_toNat' _))
    d1 (by omega) (by rw [h0.hrd]; simp) h0.dd h0.wd) fun t4 ⟨l4, k4⟩ => ?_
  have R4 := R3.of_keep k4
  -- `p`.
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (ldStep_ok l4 (j := aP) (by decide) rfl (by decide) R4.s3 (R4.s4.trans (ofNat_toNat' _))
    p1 (by omega) (by rw [h0.hrd]; simp) h0.dp h0.wp) fun t5 ⟨l5, k5⟩ => ?_
  have R5 := R4.of_keep k5
  -- `q`.
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (ldStep_ok l5 (j := aQ) (by decide) rfl (by decide) R5.s5 (R5.s6.trans (ofNat_toNat' _))
    q1 (by omega) (by rw [h0.hrd]; simp) h0.dq h0.wq) fun t6 ⟨l6, k6⟩ => ?_
  have R6 := R5.of_keep k6
  -- `dP`.
  rw [kc_seqs_cons (by simp)]
  have ddp := h0.ddp; have wdp := h0.wdp
  simp only [rgS, ckScr, h0.hdp] at ddp
  rw [h0.hdp] at wdp
  refine WP.mono (ldStep_ok l6 (j := aDP) (by decide) rfl (by decide) R6.a2 (R6.s4.trans (ofNat_toNat' _))
    p1 (by omega) (by rw [h0.hrd, ← h0.hdp]; simp) ddp wdp) fun t7 ⟨l7, k7⟩ => ?_
  have R7 := R6.of_keep k7
  -- `dQ`.
  rw [kc_seqs_cons (by simp)]
  have ddq := h0.ddq; have wdq := h0.wdq
  simp only [rgS, ckScr, h0.hdq] at ddq
  rw [h0.hdq] at wdq
  refine WP.mono (ldStep_ok l7 (j := aDQ) (by decide) rfl (by decide) R7.a3 (R7.s6.trans (ofNat_toNat' _))
    q1 (by omega) (by rw [h0.hrd, ← h0.hdq]; simp) ddq wdq) fun t8 ⟨l8, k8⟩ => ?_
  have R8 := R7.of_keep k8
  -- `qInv`.
  rw [kc_seqs_cons (by simp [start])]
  have dqi := h0.dqi; have wqi := h0.wqi
  simp only [rgS, ckScr, h0.hqi] at dqi
  rw [h0.hqi] at wqi
  refine WP.mono (ldStep_ok l8 (j := aQI) (by decide) rfl (by decide) R8.a6 (R8.s4.trans (ofNat_toNat' _))
    p1 (by omega) (by rw [h0.hrd, ← h0.hqi]; simp) dqi wqi) fun t9 ⟨l9, k9⟩ => ?_
  have R9 := R8.of_keep k9
  -- The checks.
  let g : Geo := ⟨stackArg s0 8, (stackArg s0 9).toNat * 8, (s0.gpr .a1).toNat⟩
  let v : Vals := ⟨Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a0) (s0.gpr .a1).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a2) (s0.gpr .a3).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a6) (s0.gpr .a7).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (stackArg s0 0) (stackArg s0 1).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (stackArg s0 2) (s0.gpr .a7).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (stackArg s0 4) (stackArg s0 1).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (stackArg s0 6) (s0.gpr .a7).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a4) (s0.gpr .a5).toNat)⟩
  have a9 : Arrs t9.mem g.B g.w (vals v) live0 := l9.arrs.sub (by decide)
  rw [List.nil_append, kc_seqs_append (l₁ := start) (by simp [start]) (by simp [crtChecks, eqA])]
  refine WP.mono (start_ok (g := g) (v := v) l9.ws a9 (l9.top _ (by decide))) fun t10 ⟨X₁, X₂, hX, g10⟩ => ?_
  rw [kc_seqs_append (l₁ := crtChecks) (by simp [crtChecks, eqA]) (by simp [dChecks, ltA])]
  refine WP.mono (crtChecks_ok g10 ⟨(stackArg s0 1).toNat, q1, by omega, lt_pow8_of_len _ (len_bytes _ _ _),
    R9.s6.trans (ofNat_toNat' _)⟩) fun t11 ⟨R₁, R₂, R₃, hR₁, hR₂, hR₃, g11⟩ => ?_
  rw [kc_seqs_append (l₁ := dChecks) (by simp [dChecks, ltA]) (by simp)]
  refine WP.mono (dChecks_ok g11) fun t12 ⟨Y₁, Y₂, hY₁, hY₂, A, live, g12⟩ => ?_
  rw [show seqs [.block ret] = .block ret from rfl]
  refine WP.mono (ret_ok g12) fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨(g12.base l9.base).of_regs kt tm, ?_⟩
  rw [t3]
  congr 2
  have e := ck_bits (k := (s0.gpr .a1).toNat) (w := g.w) hmv hev
    (lt_pow_of_len _ (by rw [len_bytes]; exact p2)) (lt_pow_of_len _ (by rw [len_bytes]; exact q2))
    (by have := hp.k64; omega) (pow_kw _) hX hR₁ hR₂ hR₃ hY₁ hY₂
  rw [show ckOk s0 = Spec.Rsa.keyValid (s0.gpr .a1).toNat _ _ _ _ _ _ _ _ by
    simp only [ckOk, Spec.Rsa.checkKey, len_bytes]; rfl, e]
  rfl

theorem ckOk_valid {s0 : State} (h : ckOk s0 = true) :
    Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a2) (s0.gpr .a3).toNat)) = true ∧
      Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a0) (s0.gpr .a1).toNat))
        (s0.gpr .a1).toNat = true := by
  simp only [ckOk, Spec.Rsa.checkKey, Spec.Rsa.keyValid, len_bytes, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.1.1.1.1⟩

/-- `vg_rsa_check_key`: the registers restored, and `checkKey` returned. -/
theorem ck_main {s0 : State} (h0 : CkP s0) :
    WP isa VG.Impl.Rsa.RISCV64.CheckKey.code s0 fun t =>
      (∀ i < 12, t.gpr (saved i) = s0.gpr (saved i)) ∧ t.gpr .a0 = BitVec.ofNat 64 (if ckOk s0 then 1 else 0) := by
  have hp := ck_kpre h0
  have hk := hp.k1024
  have e2 := h0.e2
  unfold VG.Impl.Rsa.RISCV64.CheckKey.code
  show WP isa (fn (8 * 8) _ _ _) s0 _
  exact fn_ok hp (by decide) (MV := CkRegs s0) (ck_moves_ok h0) h0.e1 (by omega) (by rw [h0.hrd]; simp)
    h0.de h0.we (by rw [h0.hrd]; simp) h0.dn h0.wn ckOk_valid
    fun v t mv kt bt h4 ev mv' => ck_valid h0 bt (mv.of_keep kt) h4 ev mv'

theorem pres_saved : ∀ r ∈ preserved, ∃ i < 12, r = saved i := by decide

/-- What `vg_rsa_check_key` returns. -/
def ckPost (s s' : State) : Prop := (s'.gpr .a0).setWidth 32 = if ckOk s then 1 else 0

theorem ck_correct (s : State) (hpre : (Spec.Rsa.checkKeyContract RISCV64.abi).pre s) :
    ∃ tr t, Exec isa VG.Impl.Rsa.RISCV64.CheckKey.code s tr t ∧ abiPreserved s t ∧ ckPost s t := by
  show WP isa VG.Impl.Rsa.RISCV64.CheckKey.code s fun t => abiPreserved s t ∧ ckPost s t
  refine WP.mono (WP.rdwr (WP.keep fnRegs (ck_main (ckP_of hpre)) (by rfl) (by rfl)))
    fun t ⟨⟨⟨hs, ha⟩, k⟩, _, _, hsp⟩ => ⟨⟨fun r hr => ?_, hsp, k.gpr (by decide)⟩, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := pres_saved r hr
    exact hs i hi
  · unfold ckPost
    rw [ha]
    cases ckOk s <;> rfl

end VG.Proof.Rsa.RISCV64.KeyCheck
