module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvArithB
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvArithC
public import VerifiedGarbage.Proof.Rsa.CrtValuesMask
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.MontCheckMath

/-!
# `vg_rsa_crt_values` on PPC64LE: the arithmetic

`arith_ok`: from `ArInit`, the mask of the checks is `maskOf p q X₁ X₂ V`
for the quotient and remainder `X₁`, `X₂` of `n` by `p` (when `p > 0`:
`partA` checks `p q = n` by products, `MontCheckMath.maskM_iff`) and
the gcd `V` of `q` and `m = p | 1` (when `m > 1`), with `qInv` in array 3
and the remainders of `d` by `p - 1` and `q - 1` (with their low bits
cleared) in `aDR2` and `aDR3`: what `Proof/Rsa/CrtValuesMath.lean`'s
`crtKey_masked` takes.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs aM aNM aZero aT1 aT2 aT3 aT4 sOdd sB sC)
open VG.Impl.Rsa.PPC64LE.CrtValues (arith sPodd sE1 sE2 sE3 sMask aOne aQ aP aDQ aDR aDD aDT aDR2 aDR3 aD
  nArr)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)
open VG.Proof.Rsa.CrtValues (maskOf)

theorem arith_eq : arith = seqs (partA ++ (partB ++ partC)) := rfl

/-- The arrays and slots `arith` writes. -/
abbrev arithArrs : List Nat := partAArrs ++ partBArrs ++ [aDR2, aDR3, aDQ]
abbrev arithSlots : List Nat := partASlots ++ partBSlots

/-- The registers `arith` changes. -/
abbrev arithRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem arith_ok [InvLaw] {s : State} {B : Addr} {Z w Nv P Q Dd pL qL : Nat} (h : Ws s B Z w nArr)
    (hi : ArInit s.mem B w Nv P Q Dd) (hw : 10 ≤ w) (h20 : s.gpr .r20 = BitVec.ofNat 64 pL)
    (h22 : s.gpr .r22 = BitVec.ofNat 64 qL) (hpL : 1 ≤ pL) (hqL : 1 ≤ qL) (hpw : pL ≤ 4 * w) (hqw : qL ≤ 4 * w)
    (hP : P < 2 ^ (8 * pL)) (hQ : Q < 2 ^ (8 * qL)) (hQN : Q < Nv) :
    WP isa arith s fun t => Ws t B Z w nArr ∧ KeyWorkspace.Keep B w arithArrs arithSlots s.mem t.mem ∧
      (∃ X₁ X₂ V, slot t.mem B sMask = (if maskOf P Q X₁ X₂ V then 1 else 0) ∧
        (0 < P → X₁ = Nv / P ∧ X₂ = Nv % P) ∧
        (1 < modOf P → V = Nat.gcd Q (modOf P) ∧
          ((modOf P : Nat) : Int) ∣ (num t.mem B w 3 : Int) * Q - V ∧ num t.mem B w 3 < modOf P)) ∧
      (0 < 2 * (P / 2) → (KeyCheck.Shape w pL qL → 2 ^ (64 * (w / 4 - 1)) ≤ 2 * (P / 2)) →
        num t.mem B w aDR2 = Dd % (2 * (P / 2))) ∧
      (0 < 2 * (Q / 2) → (KeyCheck.Shape w pL qL → 2 ^ (64 * (w / 4 - 1)) ≤ 2 * (Q / 2)) →
        num t.mem B w aDR3 = Dd % (2 * (Q / 2))) ∧
      Keep arithRegs s t := by
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  rw [arith_eq, wp_seqs_append (by unfold partA; exact List.cons_ne_nil _ _)
    (by unfold partB; exact List.cons_ne_nil _ _)]
  have hpw' : pL < 2 ^ 32 := by have := h.wle; omega_arith
  refine WP.mono (partA_ok h hi h20 hpL hpw hP) fun t1 ⟨h1, k1, o1, e1, b2, hM, top1, r1⟩ => ?_
  have keepA : ∀ j, j < nArr → j ∉ partAArrs → num t1.mem B w j = num s.mem B w j := fun j hj hn =>
    k1.num (fun x hx e => hn (by subst e; exact hx)) (by decide) (fit _ hj)
  rw [wp_seqs_append (by unfold partB; exact List.cons_ne_nil _ _)
    (by unfold partC; exact List.cons_ne_nil _ _)]
  have z1 : ∀ j ∈ ([0, 1, 2, 3, aM, aNM, aZero, aOne] : List Nat), num t1.mem B w j = 0 := by
    intro j hj
    have hj' : j < 25 ∧ j ≠ aDQ ∧ j ≠ aP ∧ j ≠ aQ ∧ j ≠ aD ∧ j ∉ partAArrs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨a, b, c, d, e, f⟩ := hj'
    rw [keepA j a f, hi.zero j a b c d e]
  have bo : slot t1.mem B sPodd ≤ 1 := by rw [o1]; omega_arith
  have b1 : slot t1.mem B sE1 ≤ 1 := by rw [e1]; split <;> omega_arith
  refine WP.mono (partB_ok (P := P) (Q := Q) h1 hw (by rw [keepA _ (by decide) (by decide), hi.q])
    (by rw [keepA _ (by decide) (by decide), hi.p]) z1 bo b1 b2 (by rw [r1.gpr _ (by decide), h20])
    (by rw [r1.gpr _ (by decide), h22]) hpL hpw hqw hP hQ) fun t2 ⟨h2, k2, m2, v2, r2⟩ => ?_
  have top2 : w32 t2.mem B (arr w aDD + 4 * w) = 0 := by
    rw [KeyWorkspace.Keep.word k2 (i := w) (by omega_arith) (by decide) (by decide) (fit _ (by decide)), top1]
  have p2' : num t2.mem B w aP = P := by
    rw [k2.num (by decide) (by decide) (fit _ (by decide)), keepA _ (by decide) (by decide), hi.p]
  have q2' : num t2.mem B w aQ = Q := by
    rw [k2.num (by decide) (by decide) (fit _ (by decide)), keepA _ (by decide) (by decide), hi.q]
  have hqw' : qL < 2 ^ 32 := by have := h.wle; omega_arith
  refine WP.mono (partC_ok h2 top2 (by rw [r2.gpr _ (by decide), r1.gpr _ (by decide), h20])
    (by rw [r2.gpr _ (by decide), r1.gpr _ (by decide), h22]) hpL hqL hpw' hqw' (by rw [p2']; exact hP)
    (by rw [q2']; exact hQ)) fun t ⟨h4, k4, v3, v4, r4⟩ => ?_
  -- What the later parts keep.
  have n2 : ∀ j, j < nArr → j ∉ partBArrs → num t2.mem B w j = num t1.mem B w j := fun j hj hn =>
    k2.num (fun x hx e => hn (by subst e; exact hx)) (by decide) (fit _ hj)
  have n4 : ∀ j, j < nArr → j ∉ [aDQ, aDD, aDR2, aDT, aDR3] → num t.mem B w j = num t2.mem B w j :=
    fun j hj hn => k4.num (fun x hx e => hn (by subst e; exact hx)) (by simp) (fit _ hj)
  have d2 : num t2.mem B w aD = Dd := by rw [n2 _ (by decide) (by decide), keepA _ (by decide) (by decide), hi.d]
  refine ⟨h4, ?_, ⟨Nv / P, Nv % P, num t2.mem B w 1, ?_, fun _ => ⟨rfl, rfl⟩, fun hm => ?_⟩, ?_, ?_,
    ((r1.trans r2).trans r4).mono⟩
  · exact k1.mono.trans (k2.mono.trans k4.mono)
  · have hqW : Q < 2 ^ (32 * w) := by rw [← hi.q]; exact val32_lt _ _ _ _
    have hnW : Nv < 2 ^ (32 * w) := by rw [← hi.n]; exact val32_lt _ _ _ _
    have key := VG.Proof.Rsa.maskM_iff (P := P) (Q := Q) (N := Nv) (L := P * Q % 2 ^ (32 * w))
      (M := if slot t1.mem B sE2 = 1 then 0 else 1) (V := num t2.mem B w 1) (j := 32 * w) hQN hqW hnW rfl
      (fun podd p2 => by rw [← hM podd p2]; split <;> simp_all)
    have iff : (slot t1.mem B sPodd = 1 ∧ slot t1.mem B sE1 = 1 ∧ slot t1.mem B sE2 = 1 ∧
        num t2.mem B w 1 = 1) ↔ maskOf P Q (Nv / P) (Nv % P) (num t2.mem B w 1) = true := by
      simp only [maskOf, decide_eq_true_eq]
      rw [← key, o1, e1]
      constructor
      · rintro ⟨a, b, c, d⟩
        refine ⟨a, ?_, by simp [c], d⟩
        by_contra hne; simp [hne] at b
      · rintro ⟨a, b, c, d⟩
        refine ⟨a, by simp [b], ?_, d⟩
        by_contra hne; simp [hne] at c
    rw [KeyWorkspace.Keep.slot k4 (by decide) (by simp), m2]
    by_cases hc : maskOf P Q (Nv / P) (Nv % P) (num t2.mem B w 1) = true
    · rw [ite_eq_left (iff.2 hc), ite_eq_left hc]
    · rw [ite_eq_right (fun x => hc (iff.1 x)), ite_eq_right hc]
  · obtain ⟨g, dv, lt⟩ := v2 hm
    rw [n4 3 (by decide) (by decide)]
    exact ⟨g, dv, lt⟩
  · intro hP hb
    rw [v3 (by rw [p2']; exact hP) (by rw [p2']; exact hb), d2, p2']
  · intro hQ hb
    rw [v4 (by rw [q2']; exact hQ) (by rw [q2']; exact hb), d2, q2']

end VG.Proof.Rsa.PPC64LE.CrtValues
