module

import VerifiedGarbage.Proof.Rsa.PPC64LE.CvArithA
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Rsa.PPC64LE.CrtValues
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLoop

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

/-- The second part of `arith`. -/
def partB : List (Prog isa) :=
  invSetup ++ [inverse, eqS sE3 1 aOne,
    .block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3)]

/-- The arrays and slots `partB` writes. -/
abbrev partBArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, aT1, aT2, aT3, aT4, aM, aNM, aOne]
abbrev partBSlots : List Nat := [sOdd, sB, sC, sE3, sMask]

/-- `m = p | 1`. -/
abbrev modOf (P : Nat) : Nat := 2 * (P / 2) + 1

theorem partB_ok {s : State} {B : Addr} {Z w P Q : Nat} (h : Ws s B Z w nArr)
    (hq : num s.mem B w aQ = Q) (hp : num s.mem B w aP = P)
    (z : ∀ j ∈ ([0, 1, 2, 3, aM, aNM, aZero, aOne] : List Nat), num s.mem B w j = 0)
    (bo : slot s.mem B sPodd ≤ 1) (b1 : slot s.mem B sE1 ≤ 1) (b2 : slot s.mem B sE2 ≤ 1) :
    WP isa (seqs partB) s fun t => Ws t B Z w nArr ∧
      KeyWorkspace.Keep B w partBArrs partBSlots s.mem t.mem ∧
      slot t.mem B sMask = (if slot s.mem B sPodd = 1 ∧ slot s.mem B sE1 = 1 ∧ slot s.mem B sE2 = 1 ∧
        num t.mem B w 1 = 1 then 1 else 0) ∧
      (1 < modOf P → num t.mem B w 1 = Nat.gcd Q (modOf P) ∧
        ((modOf P : Nat) : Int) ∣ (num t.mem B w 3 : Int) * Q - num t.mem B w 1 ∧
        num t.mem B w 3 < modOf P) ∧
      Keep invRegs s t := by
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have wp := h.wpos
  have fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have zero : ∀ j, j ∈ ([0, 1, 2, 3, aM, aNM, aZero, aOne] : List Nat) → num s.mem B w j = 0 := z
  unfold partB invSetup
  simp only [List.cons_append, List.nil_append]
  -- 1: `u = q`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (by decide) (by decide) (by decide) (by decide)) fun t1 ⟨h1, k1, v1, r1, _⟩ => ?_
  -- 2, 3: `m = p | 1`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h1 (by decide) (by decide) (by decide) (by decide)) fun t2 ⟨h2, k2, v2, r2, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil (orOne aM)]
  refine orOne_ok h2 (by decide) (by decide) fun t3 h3 k3 v3 r3 => WP.block_nil ?_
  have p1 : num t1.mem B w aP = P := by rw [k1.num (by decide) (by simp) (fit _ (by decide)), hp]
  rw [v2, p1] at v3
  -- 4: `v = m`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h3 (by decide) (by decide) (by decide) (by decide)) fun t4 ⟨h4, k4, v4, r4, _⟩ => ?_
  rw [v3] at v4
  -- 5: `x₁ = 1` and `[aOne] = 1`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine setOne_ok h4 (by decide) (by decide) fun t5' h5' k5' v5' r5' => ?_
  rw [← List.append_nil (setOne aOne)]
  refine setOne_ok h5' (by decide) (by decide) fun t5 h5 k5 v5 r5 => WP.block_nil ?_
  -- What the copies kept.
  have z2 : num t4.mem B w 2 = 0 := by
    rw [k4.num (by decide) (by simp) (fit _ (by decide)), k3.num (by decide) (by simp) (fit _ (by decide)),
      k2.num (by decide) (by simp) (fit _ (by decide)), k1.num (by decide) (by simp) (fit _ (by decide)),
      zero 2 (by decide)]
  have zO : num t5'.mem B w aOne = 0 := by
    rw [k5'.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
      k3.num (by decide) (by simp) (fit _ (by decide)), k2.num (by decide) (by simp) (fit _ (by decide)),
      k1.num (by decide) (by simp) (fit _ (by decide)), zero aOne (by decide)]
  rw [z2] at v5'
  rw [zO] at v5
  simp only [Nat.zero_div, Nat.mul_zero, Nat.add_zero] at v5' v5
  -- 6: the negated modulus.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t6 ⟨h6, k6, v6, b6, r6⟩ => ?_
  have m5 : num t5.mem B w aM = modOf P := by
    rw [k5.num (by decide) (by simp) (fit _ (by decide)), k5'.num (by decide) (by simp) (fit _ (by decide)),
      k4.num (by decide) (by simp) (fit _ (by decide)), v3]
  have zZ : ∀ {m : Mem} {js ds : List Nat}, KeyWorkspace.Keep B w js ds s.mem m → aZero ∉ js →
      (∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) → num m B w aZero = 0 := fun k hj hd => by
    rw [k.num (fun x hx e => hj (by subst e; exact hx)) hd (fit _ (by decide)), zero aZero (by decide)]
  have K5 : KeyWorkspace.Keep B w [0, aM, 1, 2, aOne] [] s.mem t5.mem :=
    k1.mono.trans (k2.mono.trans (k3.mono.trans (k4.mono.trans (k5'.mono.trans k5.mono))))
  have z5 : num t5.mem B w aZero = 0 := zZ K5 (by decide) (by simp)
  rw [z5, m5] at v6
  have m6 : num t6.mem B w aM = modOf P := by rw [k6.num (by decide) (by simp) (fit _ (by decide)), m5]
  have nm6 : num t6.mem B w aNM + num t6.mem B w aM = 2 ^ (32 * w) := by
    rw [m6]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b6 with e | e <;>
      rw [e] at v6 <;> simp only [modOf] at v6 ⊢ <;> omega
  have z6 : num t6.mem B w aZero = 0 := by rw [k6.num (by decide) (by simp) (fit _ (by decide)), z5]
  have bank6 : bank t6.mem B w 0 = (num t6.mem B w 0, num t6.mem B w aM, 1, 0) := by
    have e0 : num t6.mem B w 0 = num t1.mem B w 0 := by
      rw [k6.num (by decide) (by simp) (fit _ (by decide)), k5.num (by decide) (by simp) (fit _ (by decide)),
        k5'.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
        k3.num (by decide) (by simp) (fit _ (by decide)), k2.num (by decide) (by simp) (fit _ (by decide))]
    have e1 : num t6.mem B w 1 = modOf P := by
      rw [k6.num (by decide) (by simp) (fit _ (by decide)), k5.num (by decide) (by simp) (fit _ (by decide)),
        k5'.num (by decide) (by simp) (fit _ (by decide)), v4]
    have e2 : num t6.mem B w 2 = 1 := by
      rw [k6.num (by decide) (by simp) (fit _ (by decide)), k5.num (by decide) (by simp) (fit _ (by decide)), v5']
    have e3 : num t6.mem B w 3 = 0 := by
      rw [k6.num (by decide) (by simp) (fit _ (by decide)), K5.num (by decide) (by simp) (fit _ (by decide)),
        zero 3 (by decide)]
    simp only [bank, e1, e2, e3, m6]
  -- 7: `inverse`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (inverse_ok h6 (by decide) (by decide)) fun t7 ⟨h7, k7, r7, v7⟩ => ?_
  have q6 : num t6.mem B w 0 = Q := by
    rw [k6.num (by decide) (by simp) (fit _ (by decide)), k5.num (by decide) (by simp) (fit _ (by decide)),
      k5'.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
      k3.num (by decide) (by simp) (fit _ (by decide)), k2.num (by decide) (by simp) (fit _ (by decide)), v1, hq]
  -- 8: whether the gcd is 1.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h7 (by decide) (by decide) (by decide) (by decide)) fun t8 ⟨h8, k8, e8, r8⟩ => ?_
  have o7 : num t7.mem B w aOne = 1 := by
    rw [k7.num (by decide) (by decide) (fit _ (by decide)), k6.num (by decide) (by simp) (fit _ (by decide)), v5]
  rw [o7] at e8
  -- 9: the mask.
  have K8 : KeyWorkspace.Keep B w partBArrs partBSlots s.mem t8.mem :=
    K5.mono.trans (k6.mono.trans (k7.mono.trans k8.mono))
  have so : slot t8.mem B sPodd = slot s.mem B sPodd := K8.slot (by decide) (by decide)
  have s1 : slot t8.mem B sE1 = slot s.mem B sE1 := K8.slot (by decide) (by decide)
  have s2 : slot t8.mem B sE2 = slot s.mem B sE2 := K8.slot (by decide) (by decide)
  rw [List.append_assoc, ← List.append_nil (andS sMask sMask sE3)]
  refine andS_ok h8 (by decide) (by decide) (by decide) (by rw [so]; exact bo) (by rw [s1]; exact b1)
    fun t9 h9 k9 e9 r9 => ?_
  refine andS_ok h9 (by decide) (by decide) (by decide) (by rw [e9]; split <;> omega)
    (by rw [k9.slot (by decide) (by decide), s2]; exact b2) fun t10 h10 k10 e10 r10 => ?_
  refine andS_ok h10 (by decide) (by decide) (by decide) (by rw [e10]; split <;> omega)
    (by rw [k10.slot (by decide) (by decide), k9.slot (by decide) (by decide), e8]; split <;> omega)
    fun t h11 k11 e11 r11 => WP.block_nil ?_
  have n7 : ∀ j, j < nArr → num t.mem B w j = num t8.mem B w j := fun j hj => by
    rw [k11.num (by simp) (by simp; decide) (fit _ hj), k10.num (by simp) (by simp; decide) (fit _ hj),
      k9.num (by simp) (by simp; decide) (fit _ hj)]
  have n8 : ∀ j, j < nArr → num t8.mem B w j = num t7.mem B w j := fun j hj =>
    k8.num (by simp) (by simp; decide) (fit _ hj)
  refine ⟨h11, K8.trans (k9.mono.trans (k10.mono.trans k11.mono)), ?_, fun h1M => ?_,
    ((((((((((r1.trans r2).trans r3).trans r4).trans r5').trans r5).trans r6).trans r7).trans r8).trans
      ((r9.trans r10).trans r11))).mono⟩
  · rw [e11, e10, e9, so, s1, k9.slot (e := sE2) (by decide) (by decide), s2,
      k10.slot (e := sE3) (by decide) (by decide), k9.slot (e := sE3) (by decide) (by decide), e8,
      n7 1 (by decide), n8 1 (by decide)]
    by_cases a : slot s.mem B sPodd = 1 <;> by_cases b : slot s.mem B sE1 = 1 <;>
      by_cases c : slot s.mem B sE2 = 1 <;> by_cases d : num t7.mem B w 1 = 1 <;> simp [a, b, c, d]
  · have H := v7 nm6 z6 (by rw [m6]; simp only [modOf]; omega) (by rw [m6]; exact h1M) bank6
    rw [m6, q6] at H
    rw [n7 1 (by decide), n7 3 (by decide), n8 1 (by decide), n8 3 (by decide)]
    exact H

end VG.Proof.Rsa.PPC64LE.CrtValues
