module

import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRounds
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish64
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE VG.Impl.Bignum

theorem shl1_ofNat (w : Nat) : BitVec.ofNat 64 w <<< 1 = BitVec.ofNat 64 (2 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- A digit is the low half of the word there. -/
theorem w32_eq_mod (m : Mem) (B : Addr) (d : Nat) : w32 m B d = (word m B d).toNat % 2 ^ 32 := by
  have h2 : w32 m B d < 2 ^ 32 := (m.readW (off B d) 32).isLt
  rw [word_eq_w32, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]

/-- The registers `tail` writes. -/
def tailRegs : List Reg :=
  [.r0, .r3, .r4, .r6, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22]

/-- Everything the multiplication does after loading the bases (`tail`): `[o] < m` and
`[o] 2^(64 w) ≡ [a] [b] (mod m)`, with only arrays 2, 3 and `o` changed. The
code sets the rounds' count itself, and computes `-m⁻¹ mod 2⁶⁴` from any
`r12` that `hinv` holds of: the hypotheses on `r4` and on the size of `r12`
(`_i4`, `_i12`) are those its callers prove. -/
theorem tailN_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {n o a b : Nat} (hn : 4 ≤ n) (ho : o < n) (ha : a < n) (hb : b < n) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2)
    (hb2 : b ≠ 2) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w n ≤ Z)
    (i5 : s.gpr .r5 = off B (slot w o)) (i6 : s.gpr .r6 = off B (slot w a))
    (i7 : s.gpr .r7 = off B (slot w b)) (i8 : s.gpr .r8 = off B (slot w 2))
    (i9 : s.gpr .r9 = off B (slot w 3)) (i10 : s.gpr .r10 = off B (slot w 0))
    (i11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (_i4 : s.gpr .r4 = BitVec.ofNat 64 (2 * w))
    (_i12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem B (slot w b) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa tail s fun t =>
      (val32 t.mem B (slot w o) (2 * w) < val32 s.mem B (slot w 0) (2 * w) ∧
        val32 t.mem B (slot w o) (2 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          val32 s.mem B (slot w a) (2 * w) * val32 s.mem B (slot w b) (2 * w) %
            val32 s.mem B (slot w 0) (2 * w) ∧
        Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))] s.mem t.mem) ∧
      Keep tailRegs s t := by
  have hnw := hs.nowrap
  have sl : ∀ j < n, slot w j + 8 * (w + 2) ≤ Z := fun j hj => by
    have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ n by omega_using [hj])
    rw [Nat.add_mul, Nat.one_mul] at this
    unfold slot at hZ ⊢; omega_using [this, hZ]
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  have hdr56 : 56 + 4 ≤ slot w 2 := by have := hdr_lt_slot w 2 (i := 7) (by decide); omega_arith
  have s0 := sl 0 (by omega_arith)
  have s2 := sl 2 (by omega_arith)
  have s3 := sl 3 (by omega_arith)
  have sa := sl a ha
  have sb := sl b hb
  have so := sl o ho
  have p20 := sp (show (2 : Nat) ≠ 0 by decide)
  have p23 := sp (show (2 : Nat) ≠ 3 by decide)
  have p30 := sp (show (3 : Nat) ≠ 0 by decide)
  have p2a := sp (Ne.symm ha2)
  have p2b := sp (Ne.symm hb2)
  have p2o := sp (Ne.symm ho2)
  have p3o := sp (Ne.symm ho3)
  have hM := val32_lt s.mem B (slot w 0) (2 * w)
  have pw : 2 ^ (32 * (2 * w)) = 2 ^ (64 * w) := by rw [← Nat.mul_assoc]
  unfold tail
  -- The accumulator := 0, and the rounds' count.
  refine WP.seq (WP.mono (zeroAcc_ok (w := w) hs i8 i11 hw' (by omega_arith)) fun s₂' ⟨hz, out₂, j4, k₂'⟩ => ?_)
  have hs₂' := hs.congr k₂'.wr
  have g₂' : ∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], s₂'.gpr r = s.gpr r := fun r hr =>
    k₂'.gpr r (by revert r hr; decide)
  have wv : ∀ (m : Mem) (j : Nat), wordsVal m B (slot w j) w = val32 m B (slot w j) (2 * w) :=
    fun m j => wordsVal_eq_val32 m B _ w
  have v₂ : ∀ {j}, j < n → j ≠ 2 → wordsVal s₂'.mem B (slot w j) w = wordsVal s.mem B (slot w j) w :=
    fun hj hne => out₂.wordsVal (by have := sp hne; omega_arith) (by have := sl _ hj; omega_arith)
  have m0₂ : Mont.word s₂'.mem B (slot w 0) = Mont.word s.mem B (slot w 0) :=
    out₂.word (by omega_arith) (by omega_arith)
  -- The rounds.
  refine WP.seq (WP.mono (rounds_ok (w := w) (da := slot w a) (dA := slot w 2) (dB := slot w b) (dM := slot w 0) hs₂'
    (by rw [g₂' .r6 (by decide), i6]) (by rw [g₂' .r8 (by decide), i8]) (by rw [g₂' .r7 (by decide), i7])
    (by rw [g₂' .r10 (by decide), i10]) (by rw [g₂' .r11 (by decide), i11]) j4
    (by rw [m0₂, g₂' .r12 (by decide)]; rw [w32_eq_mod] at hinv; exact hinv) hw2 hw' (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) hz
    (by rw [v₂ hb hb2, v₂ (by omega) (by decide), wv, wv]; exact hB))
    fun s₃ ⟨⟨tlt, teq, out₃⟩, k₃⟩ => ?_)
  rw [v₂ (by omega) (by decide)] at tlt teq
  rw [v₂ ha ha2, v₂ hb hb2] at teq
  rw [wordsVal_succ_top] at tlt teq
  have hs₃ := hs₂'.congr k₃.wr
  have g₃ : ∀ r ∈ [Reg.r5, .r8, .r9, .r10, .r11], s₃.gpr r = s.gpr r := fun r hr => by
    rw [k₃.gpr r (by revert r hr; decide), g₂' r (by revert r hr; decide)]
  have v₃ : ∀ {j}, j < n → j ≠ 2 → wordsVal s₃.mem B (slot w j) w = wordsVal s.mem B (slot w j) w :=
    fun hj hne => (out₃.wordsVal (by have := sp hne; omega_arith) (by have := sl _ hj; omega_arith)).trans
      (v₂ hj hne)
  -- `T - m`.
  refine WP.seq (WP.mono (subMod64_ok (w := w) (dA := slot w 2) (dT := slot w 3) (dM := slot w 0) hs₃
    (by rw [g₃ .r8 (by decide), i8]) (by rw [g₃ .r9 (by decide), i9]) (by rw [g₃ .r10 (by decide), i10])
    (by rw [g₃ .r11 (by decide), i11]) (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith))
    fun s₄ ⟨⟨c, hc, hD, h20⟩, out₄, k₄⟩ => ?_)
  rw [v₃ (by omega_arith) (by decide)] at hD
  have hs₄ := hs₃.congr k₄.wr
  have g₄ : ∀ r ∈ [Reg.r5, .r8, .r9, .r11], s₄.gpr r = s.gpr r := fun r hr => by
    rw [k₄.gpr r (by revert r hr; decide), g₃ r (by revert r hr; decide)]
  have accA : wordsVal s₄.mem B (slot w 2) w = wordsVal s₃.mem B (slot w 2) w :=
    out₄.wordsVal (by omega_arith) (by omega_arith)
  -- The selection.
  refine WP.mono (selectAcc64_ok (w := w) (dA := slot w 2) (dT := slot w 3) (dO := slot w o)
    (b := decide ((Mont.word s₃.mem B (slot w 2 + 8 * w)).toNat < c)) hs₄
    (by rw [g₄ .r8 (by decide), i8]) (by rw [g₄ .r9 (by decide), i9]) (by rw [g₄ .r5 (by decide), i5])
    (by rw [g₄ .r11 (by decide), i11]) (by rw [h20]; simp only [decide_eq_true_eq]) (by omega_arith) hw'
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨hv, out₅, k₅⟩ => ?_
  rw [accA] at hv
  have hM := wordsVal_lt s.mem B (slot w 0) w
  have hM0 : 0 < wordsVal s.mem B (slot w 0) w := by omega_arith
  have hres : wordsVal t.mem B (slot w o) w =
      (wordsVal s₃.mem B (slot w 2) w + 2 ^ (64 * w) * ((Mont.word s₃.mem B (slot w 2 + 8 * w)).toNat +
        2 ^ 64 * 0)) % wordsVal s.mem B (slot w 0) w := by
    rw [hv, ← VG.Proof.Bignum.csub_result hM (wordsVal_lt _ _ _ _) hc (wordsVal_lt _ _ _ _)
      (by rw [Nat.mul_zero, Nat.add_zero]; exact tlt) hD]
    by_cases h : (Mont.word s₃.mem B (slot w 2 + 8 * w)).toNat < c <;> simp [h]
  rw [Nat.mul_zero, Nat.add_zero] at hres
  rw [← wv, ← wv, ← wv, ← wv]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hres]; exact Nat.mod_lt _ hM0
  · rw [hres, Nat.mod_mul_mod, Nat.mul_comm, teq]
  · refine Outs.trans (Outs.of_outside (o := slot w 2) (n := 8 * (w + 2))
      (out₂.mono (Nat.le_refl _) (by omega_arith)) (by simp)) ?_
    refine Outs.trans (Outs.of_outside (o := slot w 2) (n := 8 * (w + 2))
      (out₃.mono (Nat.le_refl _) (by omega_arith)) (by simp)) ?_
    refine Outs.trans (Outs.of_outside (o := slot w 3) (n := 8 * (w + 2))
      (out₄.mono (Nat.le_refl _) (by omega_arith)) (by simp)) ?_
    exact Outs.of_outside (o := slot w o) (n := 8 * (w + 2)) (out₅.mono (Nat.le_refl _) (by omega_arith)) (by simp)
  · exact (((k₂'.trans k₃).trans k₄).trans k₅).mono

end VG.Proof.Bignum.PPC64LE
