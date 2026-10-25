module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvArithA
import VerifiedGarbage.Proof.Framework.Block

/-!
# `vg_rsa_crt_values` on PPC64LE: the arithmetic, `d` divided by `p - 1` and `q - 1`

`divD_ok`: `d` divided by a copy of `[a]` (`p` or `q`) with its low bit
cleared, the remainder in `[r]`. `partC_ok`: both.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy clrLow)
open VG.Impl.Rsa.PPC64LE.Div (div)
open VG.Impl.Rsa.PPC64LE.CrtValues (aQ aP aDQ aDD aDT aDR2 aDR3 aD nArr)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- `d` divided by `[a]` with its low bit cleared, into `[r]`. -/
def divD (a r : Nat) : List (Prog isa) :=
  [copy aDQ aD, copy aDD a, .block (clrLow aDD), div aDQ r aDD aDT]

theorem divD_ok {s : State} {B : Addr} {Z w a r : Nat} (h : Ws s B Z w nArr)
    (ha : a = aP ∨ a = aQ) (hr : r = aDR2 ∨ r = aDR3)
    (top : w32 s.mem B (arr w aDD + 4 * w) = 0) :
    WP isa (seqs (divD a r)) s fun t => Ws t B Z w nArr ∧
      KeyWorkspace.Keep B w [aDQ, aDD, r, aDT] [] s.mem t.mem ∧
      (0 < 2 * (num s.mem B w a / 2) →
        num t.mem B w r = num s.mem B w aD % (2 * (num s.mem B w a / 2))) ∧
      w32 t.mem B (arr w aDD + 4 * w) = 0 ∧ Keep stepRegs s t := by
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have ha' : a < nArr ∧ a ≠ aDQ ∧ a ≠ aDD ∧ a ≠ aDT ∧ a ≠ aD := by
    rcases ha with rfl | rfl <;> decide
  have hr' : r < nArr ∧ r ≠ aDQ ∧ r ≠ aDD ∧ r ≠ aDT ∧ r ≠ aD ∧ r ≠ a := by
    rcases hr with rfl | rfl <;> rcases ha with rfl | rfl <;> decide
  obtain ⟨a1, a2, a3, a4, a5⟩ := ha'
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hr'
  unfold divD
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (by decide) (by decide) (by decide) (by decide)) fun t1 ⟨h1, k1, v1, x1, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h1 (by decide) a1 (by decide) (Ne.symm a3)) fun t2 ⟨h2, k2, v2, x2, top2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil (clrLow aDD)]
  refine clrLow_ok h2 (by decide) (by decide) fun t3 h3 k3 v3 x3 top3 => WP.block_nil ?_
  have topd : w32 t3.mem B (arr w aDD + 4 * w) = 0 := by
    rw [top3, top2, KeyWorkspace.Keep.word k1 (i := w) (by omega_arith) (by decide) (by simp)
      (fit _ (by decide)), top]
  refine WP.mono (div_ok h3 (by decide) r1 (by decide) (by decide) (by decide) (Ne.symm r2) (by decide)
    (by decide) r3 r4 (by decide) topd) fun t ⟨h4, k4, x4, v4⟩ => ?_
  have a1' : num t1.mem B w a = num s.mem B w a := k1.num (by simp; exact Ne.symm a2) (by simp) (fit _ a1)
  have dd3 : num t3.mem B w aDD = 2 * (num s.mem B w a / 2) := by rw [v3, v2, a1']
  have dq3 : num t3.mem B w aDQ = num s.mem B w aD := by
    rw [k3.num (by decide) (by simp) (fit _ (by decide)), k2.num (by decide) (by simp) (fit _ (by decide)), v1]
  refine ⟨h4, ?_, fun hP => ?_, ?_, (((x1.trans x2).trans x3).trans x4).mono⟩
  · exact k1.mono.trans (k2.mono.trans (k3.mono.trans k4.mono))
  · obtain ⟨-, vr⟩ := v4 (by rw [dd3]; exact hP)
    rw [dd3, dq3] at vr
    have hlt : num1 t.mem B w r < 2 ^ (32 * w) := by
      rw [vr]
      have h1 : num s.mem B w a < 2 ^ (32 * w) := val32_lt _ _ _ _
      have h2 := Nat.mod_lt (num s.mem B w aD) hP
      omega_arith
    rw [num_of_num1 hlt, vr]
  · rw [KeyWorkspace.Keep.word k4 (i := w) (by omega_arith) (by simp; exact ⟨by decide, r3, by decide⟩) (by simp)
      (fit _ (by decide)), topd]

end VG.Proof.Rsa.PPC64LE.CrtValues
