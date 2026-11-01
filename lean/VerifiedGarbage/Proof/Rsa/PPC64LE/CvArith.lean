module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvArithB
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvArithC
public import VerifiedGarbage.Proof.Rsa.CrtValuesMask
import VerifiedGarbage.Proof.Framework.Block

/-!
# `vg_rsa_crt_values` on PPC64LE: the arithmetic

`arith_ok`: from `ArInit`, the mask of the checks is `maskOf p q X₁ X₂ V`
for the quotient and remainder `X₁`, `X₂` of `n` by `p` (when `p > 0`) and
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

theorem arith_eq : arith = seqs (partA ++ (partB ++ (divD aP aDR2 ++ divD aQ aDR3))) := rfl

/-- The arrays and slots `arith` writes. -/
abbrev arithArrs : List Nat := partAArrs ++ partBArrs ++ [aDR2, aDR3]
abbrev arithSlots : List Nat := partASlots ++ partBSlots

/-- The registers `arith` changes. -/
abbrev arithRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem arith_ok [InvLaw] {s : State} {B : Addr} {Z w Nv P Q Dd pL qL : Nat} (h : Ws s B Z w nArr)
    (hi : ArInit s.mem B w Nv P Q Dd) (hw : 10 ≤ w) (h20 : s.gpr .r20 = BitVec.ofNat 64 pL)
    (h22 : s.gpr .r22 = BitVec.ofNat 64 qL) (hpL : 1 ≤ pL) (hpw : pL ≤ 4 * w) (hqw : qL ≤ 4 * w)
    (hP : P < 2 ^ (8 * pL)) (hQ : Q < 2 ^ (8 * qL)) :
    WP isa arith s fun t => Ws t B Z w nArr ∧ KeyWorkspace.Keep B w arithArrs arithSlots s.mem t.mem ∧
      (∃ X₁ X₂ V, slot t.mem B sMask = (if maskOf P Q X₁ X₂ V then 1 else 0) ∧
        (0 < P → X₁ = Nv / P ∧ X₂ = Nv % P) ∧
        (1 < modOf P → V = Nat.gcd Q (modOf P) ∧
          ((modOf P : Nat) : Int) ∣ (num t.mem B w 3 : Int) * Q - V ∧ num t.mem B w 3 < modOf P)) ∧
      (0 < 2 * (P / 2) → num t.mem B w aDR2 = Dd % (2 * (P / 2))) ∧
      (0 < 2 * (Q / 2) → num t.mem B w aDR3 = Dd % (2 * (Q / 2))) ∧
      Keep arithRegs s t := by
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  rw [arith_eq, wp_seqs_append (by unfold partA; exact List.cons_ne_nil _ _)
    (by unfold partB; exact List.cons_ne_nil _ _)]
  refine WP.mono (partA_ok h hi) fun t1 ⟨h1, k1, o1, v1, e1, e2, top1, r1⟩ => ?_
  have keepA : ∀ j, j < nArr → j ∉ partAArrs → num t1.mem B w j = num s.mem B w j := fun j hj hn =>
    k1.num (fun x hx e => hn (by subst e; exact hx)) (by decide) (fit _ hj)
  rw [wp_seqs_append (by unfold partB; exact List.cons_ne_nil _ _)
    (by unfold divD; exact List.cons_ne_nil _ _)]
  have z1 : ∀ j ∈ ([0, 1, 2, 3, aM, aNM, aZero, aOne] : List Nat), num t1.mem B w j = 0 := by
    intro j hj
    have hj' : j < 25 ∧ j ≠ aDQ ∧ j ≠ aP ∧ j ≠ aQ ∧ j ≠ aD ∧ j ∉ partAArrs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨a, b, c, d, e, f⟩ := hj'
    rw [keepA j a f, hi.zero j a b c d e]
  have bo : slot t1.mem B sPodd ≤ 1 := by rw [o1]; omega_arith
  have b1 : slot t1.mem B sE1 ≤ 1 := by rw [e1]; split <;> omega_arith
  have b2 : slot t1.mem B sE2 ≤ 1 := by rw [e2]; split <;> omega_arith
  refine WP.mono (partB_ok (P := P) (Q := Q) h1 hw (by rw [keepA _ (by decide) (by decide), hi.q])
    (by rw [keepA _ (by decide) (by decide), hi.p]) z1 bo b1 b2 (by rw [r1.gpr _ (by decide), h20])
    (by rw [r1.gpr _ (by decide), h22]) hpL hpw hqw hP hQ) fun t2 ⟨h2, k2, m2, v2, r2⟩ => ?_
  rw [wp_seqs_append (by unfold divD; exact List.cons_ne_nil _ _) (by unfold divD; exact List.cons_ne_nil _ _)]
  have top2 : w32 t2.mem B (arr w aDD + 4 * w) = 0 := by
    rw [KeyWorkspace.Keep.word k2 (i := w) (by omega_arith) (by decide) (by decide) (fit _ (by decide)), top1]
  refine WP.mono (divD_ok h2 (.inl rfl) (.inl rfl) top2) fun t3 ⟨h3, k3, v3, top3, r3⟩ => ?_
  refine WP.mono (divD_ok h3 (.inr rfl) (.inr rfl) top3) fun t ⟨h4, k4, v4, _, r4⟩ => ?_
  -- What the later parts keep.
  have n2 : ∀ j, j < nArr → j ∉ partBArrs → num t2.mem B w j = num t1.mem B w j := fun j hj hn =>
    k2.num (fun x hx e => hn (by subst e; exact hx)) (by decide) (fit _ hj)
  have n3 : ∀ j, j < nArr → j ∉ [aDQ, aDD, aDR2, aDT] → num t3.mem B w j = num t2.mem B w j :=
    fun j hj hn => k3.num (fun x hx e => hn (by subst e; exact hx)) (by simp) (fit _ hj)
  have n4 : ∀ j, j < nArr → j ∉ [aDQ, aDD, aDR3, aDT] → num t.mem B w j = num t3.mem B w j :=
    fun j hj hn => k4.num (fun x hx e => hn (by subst e; exact hx)) (by simp) (fit _ hj)
  have p2 : num t2.mem B w aP = P := by rw [n2 _ (by decide) (by decide), keepA _ (by decide) (by decide), hi.p]
  have q3 : num t3.mem B w aQ = Q := by
    rw [n3 _ (by decide) (by decide), n2 _ (by decide) (by decide), keepA _ (by decide) (by decide), hi.q]
  have d2 : num t2.mem B w aD = Dd := by rw [n2 _ (by decide) (by decide), keepA _ (by decide) (by decide), hi.d]
  have d3 : num t3.mem B w aD = Dd := by rw [n3 _ (by decide) (by decide), d2]
  refine ⟨h4, ?_, ⟨num t1.mem B w aDQ, num t1.mem B w aDR, num t2.mem B w 1, ?_, v1, fun hm => ?_⟩, ?_, ?_,
    ((r1.trans r2).trans (r3.trans r4)).mono⟩
  · exact k1.mono.trans (k2.mono.trans (k3.mono.trans k4.mono))
  · rw [KeyWorkspace.Keep.slot k4 (by decide) (by simp), KeyWorkspace.Keep.slot k3 (by decide) (by simp), m2,
      o1, e1, e2]
    by_cases a : P % 2 = 1 <;> by_cases b : num t1.mem B w aDQ = Q <;>
      by_cases c : num t1.mem B w aDR = 0 <;> by_cases d : num t2.mem B w 1 = 1 <;>
      simp [maskOf, a, b, c, d]
  · obtain ⟨g, dv, lt⟩ := v2 hm
    rw [n4 3 (by decide) (by decide), n3 3 (by decide) (by decide)]
    exact ⟨g, dv, lt⟩
  · intro hP
    rw [n4 _ (by decide) (by decide), v3 (by rw [p2]; exact hP), d2, p2]
  · intro hQ
    rw [v4 (by rw [q3]; exact hQ), d3, q3]

end VG.Proof.Rsa.PPC64LE.CrtValues
