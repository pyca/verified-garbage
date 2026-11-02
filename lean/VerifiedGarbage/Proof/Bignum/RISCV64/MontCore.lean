module

public import VerifiedGarbage.Proof.Bignum.RISCV64.MontRounds
public import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
public import VerifiedGarbage.Proof.Bignum.Layout
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Montgomery multiplication on RISC-V: the arithmetic

`tail_ok`: `MontMul.tail`, on arrays of the working space's layout
(`Proof/Bignum/Layout.lean`), the modulus in array 0, the accumulator in
array 2 and the temporary in array 3: `[o] < m` and `[o] 2^(64 w) ≡ [a] [b]
(mod m)`, with only arrays 2, 3 and `o` changed.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum.RISCV64 VG.Impl.Bignum
open VG.Proof.Bignum (slot slot_sep Arrays)

/-- The registers `tail` writes. -/
def tailRegs : List Reg :=
  [.a0, .a1, .a3, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

theorem slot_al (w j : Nat) : slot w j % 8 = 0 := by
  unfold slot hdrBytes; rw [Nat.mul_left_comm]; omega_arith

/-- Everything `mul` does after loading the bases (`tail`), for arrays below
`n`: `[o] < m` and `[o] 2^(64 w) ≡ [a] [b] (mod m)`, with only arrays 2, 3
and `o` changed. -/
theorem tailN_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {n o a b : Nat} (hn : 4 ≤ n) (ho : o < n) (ha : a < n) (hb : b < n) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2)
    (hb2 : b ≠ 2) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w n ≤ Z)
    (i2 : s.gpr .a2 = off B (slot w o)) (i3 : s.gpr .a3 = off B (slot w a))
    (i4 : s.gpr .a4 = off B (slot w b)) (i5 : s.gpr .a5 = off B (slot w 2))
    (i6 : s.gpr .a6 = off B (slot w 3)) (i7 : s.gpr .a7 = off B (slot w 0))
    (it0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hB : wordsVal s.mem B (slot w b) w < wordsVal s.mem B (slot w 0) w) :
    WP isa tail s fun t =>
      (wordsVal t.mem B (slot w o) w < wordsVal s.mem B (slot w 0) w ∧
        wordsVal t.mem B (slot w o) w * 2 ^ (64 * w) % wordsVal s.mem B (slot w 0) w =
          wordsVal s.mem B (slot w a) w * wordsVal s.mem B (slot w b) w % wordsVal s.mem B (slot w 0) w ∧
        Arrays B w [2, 3, o] s.mem t.mem) ∧
      Keep tailRegs s t := by
  have hnw := hs.nowrap
  have sl : ∀ j < n, slot w j + 8 * (w + 2) ≤ Z := fun j hj => by
    have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ n by omega_using [hj])
    rw [Nat.add_mul, Nat.one_mul] at this
    unfold slot at hZ ⊢; omega_using [this, hZ]
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
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
  have al := slot_al w
  unfold tail
  -- The accumulator := 0, and the rounds' count.
  refine WP.seq (WP.mono (zeroAcc_ok (w := w) (dA := slot w 2) hs i5 it0 (al 2) hw' (by omega_arith))
    fun s₂' ⟨hz, out₂, j1, k₂'⟩ => ?_)
  have hs₂' := hs.congr k₂'.2.2
  have g₂' : ∀ r ∈ [Reg.a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1], s₂'.gpr r = s.gpr r := fun r hr =>
    k₂'.gpr (by revert r hr; decide)
  have v₂ : ∀ {j}, j < n → j ≠ 2 → wordsVal s₂'.mem B (slot w j) w = wordsVal s.mem B (slot w j) w :=
    fun hj hne => out₂.wordsVal (by have := sp hne; omega_arith) (by have := sl _ hj; omega_arith)
  have m0₂ : Mont.word s₂'.mem B (slot w 0) = Mont.word s.mem B (slot w 0) :=
    out₂.word (by omega_arith) (by omega_arith)
  -- The rounds.
  refine WP.seq (WP.mono (rounds_ok (w := w) (da := slot w a) (dA := slot w 2) (dB := slot w b) (dM := slot w 0) hs₂'
    (al a) (al 2) (al b) (al 0)
    (by rw [g₂' .a3 (by decide), i3]) (by rw [g₂' .a5 (by decide), i5]) (by rw [g₂' .a4 (by decide), i4])
    (by rw [g₂' .a7 (by decide), i7]) (by rw [g₂' .t0 (by decide), it0]) j1
    (by rw [m0₂, g₂' .t1 (by decide)]; exact hinv) hw2 hw' (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) hz
    (by rw [v₂ hb hb2, v₂ (by omega) (by decide)]; exact hB))
    fun s₃ ⟨⟨tlt, teq, out₃⟩, k₃⟩ => ?_)
  rw [v₂ (by omega) (by decide)] at tlt teq
  rw [v₂ ha ha2, v₂ hb hb2] at teq
  rw [wordsVal_succ_top] at tlt teq
  have hs₃ := hs₂'.congr k₃.2.2
  have g₃ : ∀ r ∈ [Reg.a2, .a5, .a6, .a7, .t0], s₃.gpr r = s.gpr r := fun r hr => by
    rw [k₃.gpr (by revert r hr; decide), g₂' r (by revert r hr; decide)]
  have v₃ : ∀ {j}, j < n → j ≠ 2 → wordsVal s₃.mem B (slot w j) w = wordsVal s.mem B (slot w j) w :=
    fun hj hne => (out₃.wordsVal (by have := sp hne; omega_arith) (by have := sl _ hj; omega_arith)).trans
      (v₂ hj hne)
  -- `T - m`.
  refine WP.seq (WP.mono (subMod64_ok (w := w) (dA := slot w 2) (dT := slot w 3) (dM := slot w 0) hs₃
    (by rw [g₃ .a5 (by decide), i5]) (by rw [g₃ .a6 (by decide), i6]) (by rw [g₃ .a7 (by decide), i7])
    (by rw [g₃ .t0 (by decide), it0]) (by omega_arith) hw' (al 2) (al 3) (al 0) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₄ ⟨⟨c, hc, hD, h20⟩, out₄, k₄⟩ => ?_)
  rw [v₃ (by omega_arith) (by decide)] at hD
  have hs₄ := hs₃.congr k₄.2.2
  have g₄ : ∀ r ∈ [Reg.a2, .a5, .a6, .t0], s₄.gpr r = s.gpr r := fun r hr => by
    rw [k₄.gpr (by revert r hr; decide), g₃ r (by revert r hr; decide)]
  have accA : wordsVal s₄.mem B (slot w 2) w = wordsVal s₃.mem B (slot w 2) w :=
    out₄.wordsVal (by omega_arith) (by omega_arith)
  -- The selection.
  refine WP.mono (selectAcc64_ok (w := w) (dA := slot w 2) (dT := slot w 3) (dO := slot w o)
    (b := decide ((Mont.word s₃.mem B (slot w 2 + 8 * w)).toNat < c)) hs₄
    (by rw [g₄ .a5 (by decide), i5]) (by rw [g₄ .a6 (by decide), i6]) (by rw [g₄ .a2 (by decide), i2])
    (by rw [g₄ .t0 (by decide), it0]) (by rw [h20]; simp only [decide_eq_true_eq]) (by omega_arith) hw'
    (al 2) (al 3) (al o) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
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
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hres]; exact Nat.mod_lt _ hM0
  · rw [hres, Nat.mod_mul_mod, Nat.mul_comm, teq]
  · refine Arrays.trans (Arrays.of_outside (j := 2) (by simp) out₂ (Nat.le_refl _) (by omega_arith)) ?_
    refine Arrays.trans (Arrays.of_outside (j := 2) (by simp) out₃ (Nat.le_refl _) (by omega_arith)) ?_
    refine Arrays.trans (Arrays.of_outside (j := 3) (by simp) out₄ (Nat.le_refl _) (by omega_arith)) ?_
    exact Arrays.of_outside (j := o) (by simp) out₅ (Nat.le_refl _) (by omega_arith)
  · exact (((k₂'.trans k₃).trans k₄).trans k₅).mono (by decide)

/-- `tailN_ok` for arrays below 8. -/
theorem tail_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2)
    (hb2 : b ≠ 2) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (i2 : s.gpr .a2 = off B (slot w o)) (i3 : s.gpr .a3 = off B (slot w a))
    (i4 : s.gpr .a4 = off B (slot w b)) (i5 : s.gpr .a5 = off B (slot w 2))
    (i6 : s.gpr .a6 = off B (slot w 3)) (i7 : s.gpr .a7 = off B (slot w 0))
    (it0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hB : wordsVal s.mem B (slot w b) w < wordsVal s.mem B (slot w 0) w) :
    WP isa tail s fun t =>
      (wordsVal t.mem B (slot w o) w < wordsVal s.mem B (slot w 0) w ∧
        wordsVal t.mem B (slot w o) w * 2 ^ (64 * w) % wordsVal s.mem B (slot w 0) w =
          wordsVal s.mem B (slot w a) w * wordsVal s.mem B (slot w b) w % wordsVal s.mem B (slot w 0) w ∧
        Arrays B w [2, 3, o] s.mem t.mem) ∧
      Keep tailRegs s t :=
  tailN_ok hs (by decide) ho ha hb ho2 ho3 ha2 hb2 hw2 hw' hZ i2 i3 i4 i5 i6 i7 it0 hinv hB

end VG.Proof.Bignum.RISCV64
