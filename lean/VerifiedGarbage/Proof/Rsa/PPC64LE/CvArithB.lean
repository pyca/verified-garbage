module

import VerifiedGarbage.Proof.Rsa.PPC64LE.CvArithA
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Rsa.PPC64LE.CrtValues
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLoop
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw

/-!
# `vg_rsa_crt_values` on PPC64LE: the arithmetic, the inverse and the mask

`partB_ok`: `inverse`'s start (`(q, m, 1, 0)` with `m = p | 1`, the negated
modulus and 1), `inverse`, whether the gcd it finds is 1, and the mask of
the four checks.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy sub3 orOne setOne andS eqS inverse aM aNM aZero aT1 aT2 aT3 aT4
  sOdd sB sC)
open VG.Impl.Rsa.PPC64LE.CrtValues (invSetup sPodd sE1 sE2 sE3 sMask aOne aQ aP nArr)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- `nCalc`: `r11 = ⌈max(p_len, q_len) / 4⌉`. -/
theorem nCalc_ok {s : State} {pL qL : Nat} (h20 : s.gpr .r20 = BitVec.ofNat 64 pL)
    (h22 : s.gpr .r22 = BitVec.ofNat 64 qL) (hp : pL < 2 ^ 62) (hq : qL < 2 ^ 62) :
    WP isa (.block VG.Impl.Rsa.PPC64LE.CrtValues.nCalc) s fun t =>
      (t.gpr .r11 = BitVec.ofNat 64 ((max pL qL + 3) / 4) ∧ t.mem = s.mem) ∧ Keep [.r0, .r3, .r11] s t := by
  refine WP.keep _ ?_ (by decide)
  prun [VG.Impl.Rsa.PPC64LE.CrtValues.nCalc, h20, h22]
  generalize hd : BitVec.ofNat 64 pL - BitVec.ofNat 64 qL = d
  have hd' : d.toNat = (2 ^ 64 - qL + pL) % 2 ^ 64 := by
    rw [← hd, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  by_cases e : qL ≤ pL
  · have : d >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; simp; omega
    rw [this, show (0#64 : BitVec 64) - 0#64 = 0#64 from rfl, BitVec.and_zero, BitVec.sub_zero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, Nat.shiftRight_eq_div_pow, Nat.max_eq_left e]
    simp only [BitVec.toNat_ofNat]
    omega
  · have : d >>> 63 = 1#64 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; simp; omega
    rw [this, show (0#64 : BitVec 64) - 1#64 = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow, hd',
      Nat.max_eq_right (by omega)]
    simp only [BitVec.toNat_ofNat]
    omega

/-- The second part of `arith`. -/
def partB : List (Prog isa) :=
  invSetup ++ [VG.Impl.Rsa.PPC64LE.InvBatch.inverse, eqS sE3 1 aOne,
    .block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3)]

/-- The arrays and slots `partB` writes. -/
abbrev partBArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, aT1, aT2, aT3, aT4, aM, aNM, aOne]
abbrev partBSlots : List Nat := [sOdd, sB, sC, sE3, sMask]

/-- `m = p | 1`. -/
abbrev modOf (P : Nat) : Nat := 2 * (P / 2) + 1

/-- The registers `partB` changes. -/
abbrev partBRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem modOf_lt {P k : Nat} (hk : 1 ≤ k) (h : P < 2 ^ k) : modOf P < 2 ^ k := by
  have : 2 ^ k % 2 = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.pow_succ, Nat.mul_mod_left]
  unfold modOf; omega

theorem partB_ok [InvLaw] {s : State} {B : Addr} {Z w P Q pL qL : Nat} (h : Ws s B Z w nArr) (hw : 10 ≤ w)
    (hq : num s.mem B w aQ = Q) (hp : num s.mem B w aP = P)
    (z : ∀ j ∈ ([0, 1, 2, 3, aM, aNM, aZero, aOne] : List Nat), num s.mem B w j = 0)
    (bo : slot s.mem B sPodd ≤ 1) (b1 : slot s.mem B sE1 ≤ 1) (b2 : slot s.mem B sE2 ≤ 1)
    (h20 : s.gpr .r20 = BitVec.ofNat 64 pL) (h22 : s.gpr .r22 = BitVec.ofNat 64 qL) (hpL : 1 ≤ pL)
    (hpw : pL ≤ 4 * w) (hqw : qL ≤ 4 * w) (hP : P < 2 ^ (8 * pL)) (hQ : Q < 2 ^ (8 * qL)) :
    WP isa (seqs partB) s fun t => Ws t B Z w nArr ∧
      KeyWorkspace.Keep B w partBArrs partBSlots s.mem t.mem ∧
      slot t.mem B sMask = (if slot s.mem B sPodd = 1 ∧ slot s.mem B sE1 = 1 ∧ slot s.mem B sE2 = 1 ∧
        num t.mem B w 1 = 1 then 1 else 0) ∧
      (1 < modOf P → num t.mem B w 1 = Nat.gcd Q (modOf P) ∧
        ((modOf P : Nat) : Int) ∣ (num t.mem B w 3 : Int) * Q - num t.mem B w 1 ∧
        num t.mem B w 3 < modOf P) ∧
      Keep partBRegs s t := by
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have wl := h.wle
  have fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  unfold partB invSetup
  simp only [List.cons_append, List.nil_append]
  -- 1: `x = q`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (by decide) (by decide) (by decide) (by decide)) fun t1 ⟨h1, k1, v1, r1, _⟩ => ?_
  -- 2, 3: `m = p | 1`, `[aOne] = 1`, the primes' digits.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h1 (by decide) (by decide) (by decide) (by decide)) fun t2 ⟨h2, k2, v2, r2, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _), List.append_assoc]
  refine orOne_ok h2 (by decide) (by decide) fun t3 h3 k3 v3 r3 => ?_
  refine setOne_ok h3 (by decide) (by decide) fun t4 h4 k4 v4 r4 => ?_
  have k04 : Keep opRegs s t4 := (((r1.trans r2).trans r3).trans r4).mono
  refine WP.mono (nCalc_ok (s := t4) (pL := pL) (qL := qL) (by rw [k04.gpr _ (by decide), h20]) (by rw [k04.gpr _ (by decide), h22])
    (by omega) (by omega)) fun t5 ⟨⟨r11, m5⟩, k5⟩ => ?_
  have h5 : Ws t5 B Z w nArr := h4.of_keep k5
  have p1 : num t1.mem B w aP = P := by rw [k1.num (by decide) (by simp) (fit _ (by decide)), hp]
  rw [v2, p1] at v3
  have q5 : num t5.mem B w 0 = Q := by
    rw [m5, k4.num (by decide) (by simp) (fit _ (by decide)), k3.num (by decide) (by simp) (fit _ (by decide)),
      k2.num (by decide) (by simp) (fit _ (by decide)), v1, hq]
  have m5' : num t5.mem B w aM = modOf P := by
    rw [m5, k4.num (by decide) (by simp) (fit _ (by decide)), v3]
  have o5 : num t5.mem B w aOne = 1 := by
    rw [m5, v4, k3.num (by decide) (by simp) (fit _ (by decide)), k2.num (by decide) (by simp) (fit _ (by decide)),
      k1.num (by decide) (by simp) (fit _ (by decide)), z aOne (by decide)]
  -- The primes' digits bound `q` and `m`.
  have hn1 : 1 ≤ (max pL qL + 3) / 4 := by omega
  have hnw : (max pL qL + 3) / 4 ≤ w := by omega
  have hQn : Q < 2 ^ (32 * ((max pL qL + 3) / 4)) :=
    Nat.lt_of_lt_of_le hQ (Nat.pow_le_pow_right (by decide) (by omega))
  have hMn : modOf P < 2 ^ (32 * ((max pL qL + 3) / 4)) :=
    modOf_lt (by omega) (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by decide) (by omega)))
  -- 4: the inverse.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (InvLaw.inverse_ok h5 (by decide) (by decide) hw r11 hn1 hnw q5 hQn m5' hMn
    (by unfold modOf; omega)) fun t7 ⟨h7, k7, r7, v7⟩ => ?_
  -- 5: whether the gcd is 1.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h7 (by decide) (by decide) (by decide) (by decide)) fun t8 ⟨h8, k8, e8, r8⟩ => ?_
  have o7 : num t7.mem B w aOne = 1 := by
    rw [k7.num (by decide) (by decide) (fit _ (by decide)), o5]
  rw [o7] at e8
  -- 6: the mask.
  have K5 : KeyWorkspace.Keep B w [0, aM, aOne] [] s.mem t5.mem := by
    rw [m5]; exact k1.mono.trans (k2.mono.trans (k3.mono.trans k4.mono))
  have K8 : KeyWorkspace.Keep B w partBArrs partBSlots s.mem t8.mem :=
    K5.mono.trans ((k7.mono (by decide)).trans k8.mono)
  have so : slot t8.mem B sPodd = slot s.mem B sPodd := K8.slot (by decide) (by decide)
  have s1 : slot t8.mem B sE1 = slot s.mem B sE1 := K8.slot (by decide) (by decide)
  have s2 : slot t8.mem B sE2 = slot s.mem B sE2 := K8.slot (by decide) (by decide)
  rw [List.append_assoc, ← List.append_nil (andS sMask sMask sE3)]
  refine andS_ok h8 (by decide) (by decide) (by decide) (by rw [so]; exact bo) (by rw [s1]; exact b1)
    fun t9 h9 k9 e9 r9 => ?_
  refine andS_ok h9 (by decide) (by decide) (by decide) (by rw [e9]; split <;> omega_arith)
    (by rw [k9.slot (by decide) (by decide), s2]; exact b2) fun t10 h10 k10 e10 r10 => ?_
  refine andS_ok h10 (by decide) (by decide) (by decide) (by rw [e10]; split <;> omega_arith)
    (by rw [k10.slot (by decide) (by decide), k9.slot (by decide) (by decide), e8]; split <;> omega_arith)
    fun t h11 k11 e11 r11' => WP.block_nil ?_
  have n7 : ∀ j, j < nArr → num t.mem B w j = num t8.mem B w j := fun j hj => by
    rw [k11.num (by simp) (by simp; decide) (fit _ hj), k10.num (by simp) (by simp; decide) (fit _ hj),
      k9.num (by simp) (by simp; decide) (fit _ hj)]
  have n8 : ∀ j, j < nArr → num t8.mem B w j = num t7.mem B w j := fun j hj =>
    k8.num (by simp) (by simp; decide) (fit _ hj)
  refine ⟨h11, K8.trans (k9.mono.trans (k10.mono.trans k11.mono)), ?_, fun h1M => ?_,
    (((((((k04.trans k5).trans r7).trans r8).trans r9).trans r10).trans r11')).mono (by decide)⟩
  · rw [e11, e10, e9, so, s1, k9.slot (e := sE2) (by decide) (by decide), s2,
      k10.slot (e := sE3) (by decide) (by decide), k9.slot (e := sE3) (by decide) (by decide), e8,
      n7 1 (by decide), n8 1 (by decide)]
    by_cases a : slot s.mem B sPodd = 1 <;> by_cases b : slot s.mem B sE1 = 1 <;>
      by_cases c : slot s.mem B sE2 = 1 <;> by_cases d : num t7.mem B w 1 = 1 <;> simp [a, b, c, d]
  · obtain ⟨g, dv, lt⟩ := v7 h1M
    rw [n7 1 (by decide), n7 3 (by decide), n8 1 (by decide), n8 3 (by decide)]
    exact ⟨g, dv, lt⟩

end VG.Proof.Rsa.PPC64LE.CrtValues
