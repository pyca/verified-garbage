module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.CrtValues
public import VerifiedGarbage.Proof.Rsa.PPC64LE.DivLoop
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLoop
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Rsa.PPC64LE.Div
public import VerifiedGarbage.Impl.Rsa.PPC64LE.Inverse
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs

/-!
# `vg_rsa_crt_values` on PPC64LE: the arithmetic, the division of `n` by `p`

The arrays at the start of `arith` (`ArInit`): `n`, `p`, `q` and `d` in
`aDQ`, `aP`, `aQ` and `aD`, every other array 0, and every array's extra
digit 0. `partA_ok`: `p`'s low bit, `n` divided by `p` (`X₁` and `X₂`), and
whether `X₁ = q` and `X₂ = 0`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy bitOf eqS aM aNM aZero aT1 aT2 aT3 aT4 sOdd sB sC)
open VG.Impl.Rsa.PPC64LE.Div (div)
open VG.Impl.Rsa.PPC64LE.CrtValues (sPodd sE1 sE2 sE3 sMask aOne aQ aP aDQ aDR aDD aDT aDR2 aDR3 aD nArr)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The arrays at the start of `arith`. -/
structure ArInit (m : Mem) (B : Addr) (w Nv P Q Dd : Nat) : Prop where
  n : num m B w aDQ = Nv
  p : num m B w aP = P
  q : num m B w aQ = Q
  d : num m B w aD = Dd
  zero : ∀ j < 25, j ≠ aDQ → j ≠ aP → j ≠ aQ → j ≠ aD → num m B w j = 0
  top : ∀ j < 25, w32 m B (arr w j + 4 * w) = 0

/-- A number of `w + 1` digits below `2^(32 w)` is its low `w` digits. -/
theorem num_of_num1 {m : Mem} {B : Addr} {w j : Nat} (h : num1 m B w j < 2 ^ (32 * w)) :
    num m B w j = num1 m B w j := by
  have e := val32_append m B (arr w j) w 1
  have hl := val32_lt m B (arr w j) w
  change val32 _ _ _ (w + 1) < _ at h
  change val32 _ _ _ w = val32 _ _ _ (w + 1)
  rw [e] at h ⊢
  have : val32 m B (arr w j + 4 * w) 1 = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m B (arr w j + 4 * w) 1) with z | z
    · exact z
    · have : 2 ^ (32 * w) ≤ 2 ^ (32 * w) * val32 m B (arr w j + 4 * w) 1 := Nat.le_mul_of_pos_right _ z
      omega_arith
  rw [this, Nat.mul_zero, Nat.add_zero]

/-- The first part of `arith`. -/
def partA : List (Prog isa) :=
  [copy aDD aP, .block (bitOf sPodd aP), div aDQ aDR aDD aDT, eqS sE1 aDQ aQ, eqS sE2 aDR aZero]

/-- The arrays and slots `partA` writes. -/
abbrev partAArrs : List Nat := [aDD, aDQ, aDR, aDT]
abbrev partASlots : List Nat := [sPodd, sE1, sE2]

theorem partA_ok {s : State} {B : Addr} {Z w Nv P Q Dd : Nat} (h : Ws s B Z w nArr)
    (hi : ArInit s.mem B w Nv P Q Dd) :
    WP isa (seqs partA) s fun t => Ws t B Z w nArr ∧
      KeyWorkspace.Keep B w partAArrs partASlots s.mem t.mem ∧
      slot t.mem B sPodd = P % 2 ∧
      (0 < P → num t.mem B w aDQ = Nv / P ∧ num t.mem B w aDR = Nv % P) ∧
      slot t.mem B sE1 = (if num t.mem B w aDQ = Q then 1 else 0) ∧
      slot t.mem B sE2 = (if num t.mem B w aDR = 0 then 1 else 0) ∧
      w32 t.mem B (arr w aDD + 4 * w) = 0 ∧ Keep stepRegs s t := by
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  unfold partA
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (by decide) (by decide) (by decide) (by decide)) fun t1 ⟨h1, k1, v1, r1, top1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil (bitOf sPodd aP)]
  refine bitOf_ok h1 (by decide) (by decide) (by decide) fun t2 h2 k2 o2 r2 => WP.block_nil ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have p1 : num t1.mem B w aP = P := by rw [k1.num (by decide) (by simp) (fit _ (by decide)), hi.p]
  have dz2 : w32 t2.mem B (arr w aDD + 4 * w) = 0 := by
    rw [KeyWorkspace.Keep.word k2 (i := w) (by omega_arith) (by simp) (by simp; decide) (fit _ (by decide)),
      top1, hi.top _ (by decide)]
  refine WP.mono (div_ok h2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) dz2) fun t3 ⟨h3, k3, r3, v3⟩ => ?_
  have n2 : num t2.mem B w aDQ = Nv := by
    rw [k2.num (by simp) (by simp; decide) (fit _ (by decide)), k1.num (by decide) (by simp) (fit _ (by decide)),
      hi.n]
  have d2 : num t2.mem B w aDD = P := by
    rw [k2.num (by simp) (by simp; decide) (fit _ (by decide)), v1, hi.p]
  rw [n2, d2] at v3
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h3 (by decide) (by decide) (by decide) (by decide)) fun t4 ⟨h4, k4, e4, r4⟩ => ?_
  refine WP.mono (eqS_ok h4 (by decide) (by decide) (by decide) (by decide)) fun t ⟨h5, k5, e5, r5⟩ => ?_
  have q3 : num t3.mem B w aQ = Q := by
    rw [k3.num (by decide) (by simp) (fit _ (by decide)), k2.num (by simp) (by simp; decide) (fit _ (by decide)),
      k1.num (by decide) (by simp) (fit _ (by decide)), hi.q]
  have z3 : num t3.mem B w aZero = 0 := by
    rw [k3.num (by decide) (by simp) (fit _ (by decide)), k2.num (by simp) (by simp; decide) (fit _ (by decide)),
      k1.num (by decide) (by simp) (fit _ (by decide)), hi.zero _ (by decide) (by decide) (by decide)
        (by decide) (by decide)]
  have qt : num t.mem B w aDQ = num t3.mem B w aDQ := by
    rw [k5.num (by simp) (by simp; decide) (fit _ (by decide)), k4.num (by simp) (by simp; decide) (fit _ (by decide))]
  have rt : num t.mem B w aDR = num t3.mem B w aDR := by
    rw [k5.num (by simp) (by simp; decide) (fit _ (by decide)), k4.num (by simp) (by simp; decide) (fit _ (by decide))]
  have r4' : num t4.mem B w aDR = num t3.mem B w aDR :=
    k4.num (by simp) (by simp; decide) (fit _ (by decide))
  have z4 : num t4.mem B w aZero = 0 := by rw [k4.num (by simp) (by simp; decide) (fit _ (by decide)), z3]
  refine ⟨h5, ?_, ?_, ?_, ?_, ?_, ?_, ((((r1.trans r2).trans r3).trans r4).trans r5).mono⟩
  · exact k1.mono.trans (k2.mono.trans (k3.mono.trans (k4.mono.trans k5.mono)))
  · rw [k5.slot (by decide) (by decide), k4.slot (by decide) (by decide), k3.slot (by decide) (by simp), o2, p1]
  · intro hP
    obtain ⟨vq, vr⟩ := v3 hP
    have hr : num1 t3.mem B w aDR < 2 ^ (32 * w) := by
      rw [vr]
      exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hP) (by rw [← hi.p]; exact Nat.le_of_lt (val32_lt _ _ _ _))
    rw [qt, rt, vq, num_of_num1 hr, vr]
    exact ⟨rfl, rfl⟩
  · rw [k5.slot (by decide) (by decide), e4, q3, qt]
  · rw [e5, r4', z4, rt]
  · rw [KeyWorkspace.Keep.word k5 (i := w) (by omega_arith) (by simp) (by simp; decide) (fit _ (by decide)),
      KeyWorkspace.Keep.word k4 (i := w) (by omega_arith) (by simp) (by simp; decide) (fit _ (by decide)),
      KeyWorkspace.Keep.word k3 (i := w) (by omega_arith) (by decide) (by simp) (fit _ (by decide)), dz2]

end VG.Proof.Rsa.PPC64LE.CrtValues
