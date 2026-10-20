module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Montgomery
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontRest
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.Bignum.Math

/-! # FFDH parameter candidates on x86-64: Montgomery encodings of 1 and −1 -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def constantRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)), (slot w aR1, 8 * w), (slot w aRm1, 8 * w)]

theorem prepareConstants_ok (M : Mont) {s₃ : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64}
    (hg : Good s₃ B Z w mi) (hZ : slot w 8 ≤ Z) (hXZ : slot w aRm1 + 8 * (w + 2) ≤ Z)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hn : wv s₃.mem B (slot w aN) w = N)
    (hinv : ((word s₃.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0)
    (hone : wv s₃.mem B (slot w aOne) w = 1) (hodd : N % 2 = 1) (hN1 : 1 < N)
    (hr2 : wv s₃.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N) :
    WP isa (prepareConstants M.mm) s₃ fun t => Good t B Z w mi ∧
      wv t.mem B (slot w aR1) w = 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aRm1) w = N - 2 ^ (64 * w) % N ∧
      Frm B (constantRanges w) s₃.mem t.mem ∧ Keep mmRegs s₃ t := by
  have hR : Nat.Coprime (2 ^ (64 * w)) N := coprime_pow2 hodd _
  have hnw := hg.scr.nowrap
  have hR1Z : slot w aR1 + 8 * (w + 2) ≤ Z :=
    Nat.le_trans (Nat.add_le_add_right (VG.Proof.Rsa.slot_mono (w := w) (by decide : aR1 ≤ aRm1)) _) hXZ
  have hR1readZ : slot w aR1 + 8 * w ≤ Z :=
    Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 8 (Nat.le_add_right w 2)) _) hR1Z
  have hR1read : slot w aR1 + 8 * w ≤ 2 ^ 64 :=
    Nat.le_trans hR1readZ (Nat.le_trans (Nat.le_add_left Z B.toNat) hnw)
  unfold prepareConstants copyR1 negateR1
  -- `R mod c`.
  refine WP.seq (WP.mono (M.mm_ok hg hZ (by omega) hw' (o := aY) (a := aR2) (b := aOne) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hinv
    (by rw [hone, hn]; exact hN1)) fun s₄ ⟨hg₄, hlt₄, hy₄, ha₄, k₄⟩ => ?_)
  rw [hn, hr2, hone] at hy₄
  rw [hn] at hlt₄
  have hY : wv s₄.mem B (slot w aY) w = 2 ^ (64 * w) % N := by
    rw [← Nat.mod_eq_of_lt hlt₄]
    refine VG.Proof.Bignum.mont_cancel hR ?_
    rw [hy₄, Nat.mul_one, Nat.mod_mod]
  have hn₄ : wv s₄.mem B (slot w aN) w = N := by rw [ha₄.wv_of_not_mem (by decide) (by decide) (by omega)]; exact hn
  -- `[aR1] := R mod c`.
  refine WP.seq (WP.mono (copyToExt_ok hg₄ hZ (by omega) hw' (a := aY) (d := aR1) (by decide) (by decide)
    hR1Z) fun s₅ ⟨hv₅, ho₅, k₅⟩ => ?_)
  rw [hY] at hv₅
  have hg₅ : Good s₅ B Z w mi := ⟨hg₄.scr.congr k₅.2.2, (k₅.gpr (by decide)).trans hg₄.rdi,
    Hdr.outside hg₄.hdr ho₅ (by unfold slot; omega)⟩
  have hout5 : ∀ {j : Nat}, j < 8 → wv s₅.mem B (slot w j) w = wv s₄.mem B (slot w j) w := fun {j} hj =>
    ho₅.wv (Or.inl (by have := slot_le (w := w) hj; have : slot w 8 ≤ slot w aR1 := (by unfold slot aR1; omega); omega))
      (by have := slot_le (w := w) hj; omega)
  -- `[aRm1] := c − R mod c`.
  refine WP.mono (msRm1_ok hg₅ hZ hXZ (by omega) hw' (by rw [hv₅, hout5 (by decide), hn₄]; exact Nat.mod_lt _ (by omega)))
    fun s₆ ⟨hv₆, ho₆, k₆⟩ => ?_
  rw [hv₅, hout5 (by decide), hn₄] at hv₆
  have hg₆ : Good s₆ B Z w mi := ⟨hg₅.scr.congr k₆.2.2, (k₆.gpr (by decide)).trans hg₅.rdi,
    Hdr.outside hg₅.hdr ho₆ (by unfold slot; omega)⟩
  refine ⟨hg₆, ?_, hv₆, ?_, ((k₄.trans k₅).trans k₆).mono (by decide)⟩
  · rw [ho₆.wv (Or.inl (by unfold slot aRm1 aR1; omega)) hR1read]
    exact hv₅
  · have f₄ : Frm B (constantRanges w) s₃.mem s₄.mem := Frm.of_arrays ha₄ (by simp [constantRanges])
    have f₅ : Frm B (constantRanges w) s₄.mem s₅.mem := Frm.of_outside ho₅ (by simp [constantRanges])
    have f₆ : Frm B (constantRanges w) s₅.mem s₆.mem := Frm.of_outside ho₆ (by simp [constantRanges])
    exact (f₄.trans f₅).trans f₆

end VG.Proof.Ffdh.X86_64.ParameterCandidate
