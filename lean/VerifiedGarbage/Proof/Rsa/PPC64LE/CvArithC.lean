module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvArithA
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.PPC64LE.DivN

/-!
# `vg_rsa_crt_values` on PPC64LE: the arithmetic, `d` divided by `p - 1` and `q - 1`

`divD_ok`: `d` divided by a copy of `[a]` (`p` or `q`) with its low bit
cleared, the remainder in `[r]`. `partC_ok`: both.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy clrLow)
open VG.Impl.Rsa.PPC64LE.Div (div divP)
open VG.Impl.Rsa.PPC64LE.CrtValues (aQ aP aDQ aDD aDT aDR2 aDR3 aD nArr)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- `d` divided by `[a]` with its low bit cleared, into `[r]`, `[a]`'s length
in bytes in `len`. -/
def divD (len : Reg) (a r : Nat) : List (Prog isa) :=
  [copy aDQ aD, copy aDD a, .block (clrLow aDD ++ [.addi .r12 len 0]), divP aDQ r aDD aDT]

theorem divD_ok {s : State} {B : Addr} {Z w a r : Nat} (h : Ws s B Z w nArr)
    (ha : a = aP ∨ a = aQ) (hr : r = aDR2 ∨ r = aDR3)
    (top : w32 s.mem B (arr w aDD + 4 * w) = 0) {len : Reg} (hlen : len = .r20 ∨ len = .r22) {L : Nat}
    (hl : s.gpr len = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hL : L < 2 ^ 32) (hlt : num s.mem B w a < 2 ^ (8 * L)) :
    WP isa (seqs (divD len a r)) s fun t => Ws t B Z w nArr ∧
      KeyWorkspace.Keep B w [aDQ, aDD, r, aDT] [] s.mem t.mem ∧
      (0 < 2 * (num s.mem B w a / 2) →
        num t.mem B w r = num s.mem B w aD % (2 * (num s.mem B w a / 2))) ∧
      w32 t.mem B (arr w aDD + 4 * w) = 0 ∧ Keep (.r12 :: stepRegs) s t := by
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
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine clrLow_ok h2 (by decide) (by decide) fun t30 h30 k30 v30 x30 top30 => ?_
  have hl0 : len ≠ .r0 := by rcases hlen with rfl | rfl <;> decide
  have l30 : t30.gpr len = BitVec.ofNat 64 L := by
    rcases hlen with rfl | rfl <;>
      rw [x30.gpr _ (by decide), x2.gpr _ (by decide), x1.gpr _ (by decide), hl]
  refine WP.mono (WP.keep [.r12] (Q := fun x => x.gpr .r12 = BitVec.ofNat 64 L ∧ x.mem = t30.mem)
    (by prun [l30, exec_addi hl0 (show 0 < 2 ^ 15 by decide), BitVec.add_zero]) (by cases len <;> decide))
    fun t3 ⟨⟨t12, tm⟩, k12⟩ => ?_
  have h3 : Ws t3 B Z w nArr := h30.of_keep k12
  have k3 := k30
  rw [← tm] at k3
  have v3 : num t3.mem B w aDD = 2 * (num t2.mem B w aDD / 2) := by rw [tm]; exact v30
  have x3 := x30.trans k12
  have topd : w32 t3.mem B (arr w aDD + 4 * w) = 0 := by
    rw [tm, top30, top2, KeyWorkspace.Keep.word k1 (i := w) (by omega_arith) (by decide) (by simp)
      (fit _ (by decide)), top]
  have a1'' : num t1.mem B w a = num s.mem B w a := k1.num (by simp; exact Ne.symm a2) (by simp) (fit _ a1)
  refine WP.mono (divP_ok h3 (by decide) r1 (by decide) (by decide) (by decide) (Ne.symm r2) (by decide)
    (by decide) r3 r4 (by decide) topd t12 hL1 hL (by rw [v3, v2, a1'']; omega_arith)) fun t ⟨h4, k4, x4, v4⟩ => ?_
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
