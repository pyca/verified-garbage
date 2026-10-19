module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Terms

import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-!
# RSA with AVX512_IFMA on x86-64: choosing an array of the region's loop

`arrLoop` runs one `to52` for each entry of `arrs`, which `arrSel` picks by
the count `r8` (`arrSel_ok`), and counts down (`subR8_ok`). The entries'
arrays and offsets fit their region and are apart (`arrs_ok`, `arrs_sep`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (se_ofNat)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- Entry `i` of `arrs`: the array. -/
abbrev arrJ (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (i : Nat) : Nat := ((arrs l).getD i (0, 0)).1

/-- Entry `i` of `arrs`: the offset in the region. -/
abbrev arrC (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (i : Nat) : Nat := ((arrs l).getD i (0, 0)).2

theorem arrs_ok (hl : LayOk l) : ∀ i < 5, arrJ l i < 8 ∧ arrC l i + l.NB ≤ l.D := by
  rcases hl with rfl | rfl | rfl <;> decide

theorem arrs_sep (hl : LayOk l) :
    ∀ k < 5, ∀ i < 5, k ≠ i → arrC l k + l.NB ≤ arrC l i ∨ arrC l i + l.NB ≤ arrC l k := by
  rcases hl with rfl | rfl | rfl <;> decide

/-- `cmp r8, k`. -/
theorem cmpR8_ok (s : State) {n k : Nat} (h8 : s.gpr .r8 = BitVec.ofNat 64 n) (hn : n < 2 ^ 31) (hk : k < 2 ^ 31) :
    WP isa (.block [.alu .cmp .r8 (.imm (BitVec.ofNat 32 k))]) s fun t =>
      t.zf = some (decide (n = k)) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.mxcsr = s.mxcsr := by
  xrun [h8, se_ofNat hk]
  exact ⟨ofNat_sub_beq (j := n) (N := k) (by omega) (by omega), rfl⟩

/-- `sub r8, 1`. -/
theorem subR8_ok (s : State) :
    WP isa (.block [.alu .sub .r8 (.imm 1)]) s fun t =>
      t.gpr .r8 = s.gpr .r8 - 1 ∧ t.zf = some (s.gpr .r8 - 1 == 0) ∧
        VG.Proof.MlKem.X86_64.Keep [.r8] s t ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r8] (Q := fun t => t.gpr .r8 = s.gpr .r8 - 1 ∧
    t.zf = some (s.gpr .r8 - 1 == 0) ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr) (by xrun; rfl) rfl)
    fun t ⟨⟨h8, hz, hm, hx⟩, k⟩ => ⟨h8, hz, k, hm, hx⟩

/-- `arrSel` from the count `r8 = ps.length - i`: `arrPtrs` of entry `i`,
from a state that differs only in the flags. -/
theorem arrSel_ok {p : Nat} {Q : State → Prop} :
    ∀ (ps : List (Nat × Nat)) (i : Nat) (s : State), i < ps.length → ps.length < 2 ^ 31 →
      s.gpr .r8 = BitVec.ofNat 64 (ps.length - i) →
      (∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.mxcsr = s.mxcsr →
        WP isa (.block (arrPtrs l p (ps.getD i (0, 0)).1 (ps.getD i (0, 0)).2)) s' Q) →
      WP isa (arrSel l p ps) s Q
  | [], _, _, hi, _, _, _ => absurd hi (Nat.not_lt_zero _)
  | [(j, o)], i, s, hi, _, _, h => by
    obtain rfl : i = 0 := by simp only [List.length_singleton] at hi; omega
    exact h s rfl rfl rfl rfl rfl
  | (j, o) :: q :: ps, i, s, hi, hl, h8, h => by
    simp only [List.length_cons] at hi hl h8
    simp only [arrSel, List.length_cons]
    refine WP.seq (WP.mono (cmpR8_ok s h8 (by omega) (by omega)) fun t ⟨hz, hg, hm, hrd, hwr, hx⟩ => ?_)
    refine WP.ite (decide (ps.length + 1 + 1 - i = ps.length + 1 + 1)) (by simp only [eval, hz])
      (fun ht => ?_) (fun hf => ?_)
    · obtain rfl : i = 0 := by simp only [decide_eq_true_eq] at ht; omega
      exact h t hg hm hrd hwr hx
    · have hi0 : i ≠ 0 := by simp only [decide_eq_false_iff_not] at hf; omega
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      exact arrSel_ok (q :: ps) i t (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
        (by rw [hg, h8]; simp only [List.length_cons]; congr 1; omega)
        fun s' hg' hm' hrd' hwr' hx' => h s' (hg'.trans hg) (hm'.trans hm) (hrd'.trans hrd) (hwr'.trans hwr)
          (hx'.trans hx)

end VG.Proof.Bignum.X86_64.Ifma
