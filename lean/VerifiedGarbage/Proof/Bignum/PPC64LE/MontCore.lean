module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRounds
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
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline

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

/-- `m' mod 2³² = y` for `m' = y (2 + m y)` and `m y ≡ -1 (mod 2³²)`. -/
theorem minv_restore_nat (A Y : Nat) (hy : Y < 2 ^ 32) (h : (A % 2 ^ 32 * Y + 1) % 2 ^ 32 = 0) :
    (A * Y % 2 ^ 64 + 2) % 2 ^ 64 * Y % 2 ^ 64 % 2 ^ 32 = Y := by
  have d : 2 ^ 32 ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by decide)
  have hAY : A * Y % 2 ^ 32 = 2 ^ 32 - 1 := by
    rw [Nat.mul_mod, Nat.mod_eq_of_lt hy]; omega_arith
  rw [Nat.mod_mod_of_dvd _ d, Nat.mul_mod, Nat.mod_mod_of_dvd _ d, Nat.add_mod, Nat.mod_mod_of_dvd _ d, hAY,
    Nat.mod_eq_of_lt hy]
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.one_mul]
  exact Nat.mod_eq_of_lt hy

/-- `restoreMinv`'s arithmetic: the low 32 bits of `m' = (m y + 2) y` are `y`. -/
theorem minv_restore (m y : BitVec 64) (hy : y.toNat < 2 ^ 32) (h : (m.toNat % 2 ^ 32 * y.toNat + 1) % 2 ^ 32 = 0) :
    ((m * y + BitVec.ofNat 64 2) * y) <<< 32 >>> 32 = y := by
  apply BitVec.eq_of_toNat_eq
  have e : ∀ x : Nat, x * 2 ^ 32 % 2 ^ 64 / 2 ^ 32 = x % 2 ^ 32 := fun x => by omega_arith
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, e,
    BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show 2 % 2 ^ 64 = 2 from rfl]
  exact minv_restore_nat m.toNat y.toNat hy h

/-- The registers `tail` writes. -/
def tailRegs : List Reg :=
  [.r0, .r3, .r4, .r6, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22]

/-- The registers `tail8` writes. -/
def tailRegs8 : List Reg := tailRegs ++ [.r21, .r28, .r29, .r30, .r31]

/-- Everything the multiplication does after loading the bases, with any rounds
`R` that do what the rounds do (`RoundsSpec`): `[o] < m` and
`[o] 2^(64 w) ≡ [a] [b] (mod m)`, with only arrays 2, 3 and `o` changed. The
code sets the rounds' count itself, and computes `-m⁻¹ mod 2⁶⁴` from any
`r12` that `hinv` holds of: the hypotheses on `r4` and on the size of `r12`
(`_i4`, `_i12`) are those its callers prove. -/
theorem tailWith_ok {R : Prog isa} (hR : RoundsSpec R) {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {n o a b : Nat} (hn : 4 ≤ n) (ho : o < n) (ha : a < n) (hb : b < n) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2)
    (hb2 : b ≠ 2) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w n ≤ Z)
    (i5 : s.gpr .r5 = off B (slot w o)) (i6 : s.gpr .r6 = off B (slot w a))
    (i7 : s.gpr .r7 = off B (slot w b)) (i8 : s.gpr .r8 = off B (slot w 2))
    (i9 : s.gpr .r9 = off B (slot w 3)) (i10 : s.gpr .r10 = off B (slot w 0))
    (i11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (_i4 : s.gpr .r4 = BitVec.ofNat 64 (2 * w))
    (_i12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem B (slot w b) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa (.seq zeroAcc (.seq R (.seq subMod64M selectAcc64))) s fun t =>
      (val32 t.mem B (slot w o) (2 * w) < val32 s.mem B (slot w 0) (2 * w) ∧
        val32 t.mem B (slot w o) (2 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          val32 s.mem B (slot w a) (2 * w) * val32 s.mem B (slot w b) (2 * w) %
            val32 s.mem B (slot w 0) (2 * w) ∧
        Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * w), (slot w o, 8 * (w + 2))] s.mem t.mem) ∧
      Keep tailRegs8 s t := by
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
  -- `m'`, the accumulator := 0, and the rounds' count.
  refine WP.seq (WP.mono (zeroAcc_ok (w := w) (dM := slot w 0) hs i8 i10 i11 hw' (by omega_arith) (by omega_arith))
    fun s₂' ⟨hz, out₂, j4, e22', w22, k₂'⟩ => ?_)
  have hs₂' := hs.congr k₂'.wr
  have g₂' : ∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], s₂'.gpr r = s.gpr r := fun r hr =>
    k₂'.gpr r (by revert r hr; decide)
  have wv : ∀ (m : Mem) (j : Nat), wordsVal m B (slot w j) w = val32 m B (slot w j) (2 * w) :=
    fun m j => wordsVal_eq_val32 m B _ w
  have v₂ : ∀ {j}, j < n → j ≠ 2 → wordsVal s₂'.mem B (slot w j) w = wordsVal s.mem B (slot w j) w :=
    fun hj hne => out₂.wordsVal (by have := sp hne; omega_arith) (by have := sl _ hj; omega_arith)
  have m0₂ : Mont.word s₂'.mem B (slot w 0) = Mont.word s.mem B (slot w 0) :=
    out₂.word (by omega_arith) (by omega_arith)
  have hinv' : ((Mont.word s.mem B (slot w 0)).toNat % 2 ^ 32 * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0 := by
    rw [w32_eq_mod] at hinv; exact hinv
  have e22 : s₂'.gpr .r22 = (Mont.word s.mem B (slot w 0) * s.gpr .r12 + BitVec.ofNat 64 2) * s.gpr .r12 := e22'
  -- The rounds.
  refine WP.seq (WP.mono (hR (w := w) (da := slot w a) (dA := slot w 2) (dB := slot w b) (dM := slot w 0) hs₂'
    (by rw [g₂' .r6 (by decide), i6]) (by rw [g₂' .r8 (by decide), i8]) (by rw [g₂' .r7 (by decide), i7])
    (by rw [g₂' .r9 (by decide), i9, show slot w 2 + 8 * (w + 2) = slot w 3 by unfold slot; omega_arith])
    (by rw [g₂' .r10 (by decide), i10]) (by rw [g₂' .r11 (by decide), i11]) j4
    (by rw [m0₂, e22]; exact mont_newton64 _ _ hinv') w22.symm hw2 hw' (by unfold slot; omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) hz
    (by rw [v₂ hb hb2, v₂ (by omega) (by decide), wv, wv]; exact hB))
    fun s₃' ⟨⟨tlt, teq, out₃, r22₃⟩, k₃'⟩ => ?_)
  -- `r12` back, at the start of `T - m`.
  show WP isa (.seq (.seq (.block (restoreMinv ++ _)) _) _) s₃' _
  rw [WP.seq_iff, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = s.gpr .r12 ∧ t.mem = s₃'.mem) (by
      unfold restoreMinv; prun [r22₃, e22, minv_restore _ _ _i12 hinv']) (by decide)) fun s₃ ⟨⟨r12₃, m₃⟩, k₃''⟩ => ?_
  rw [← WP.seq_iff, ← WP.seq_iff]
  have k₃ := k₃'.trans k₃''
  rw [← m₃] at tlt teq out₃
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
    refine Outs.trans (Outs.of_outside (o := slot w 3) (n := 8 * w) out₄ (by simp)) ?_
    exact Outs.of_outside (o := slot w o) (n := 8 * (w + 2)) (out₅.mono (Nat.le_refl _) (by omega_arith)) (by simp)
  · have K : Keep (.r12 :: tailRegs8) s t := (((k₂'.trans k₃).trans k₄).trans k₅).mono (by decide)
    have t12 : t.gpr .r12 = s.gpr .r12 := by
      rw [k₅.gpr .r12 (by decide), k₄.gpr .r12 (by decide), r12₃]
    refine ⟨fun r hr => ?_, K.rd, K.wr, K.sp, K.lr⟩
    by_cases e : r = .r12
    · subst e; exact t12
    · exact K.gpr r (by simp only [List.mem_cons, not_or]; exact ⟨e, hr⟩)


/-- Everything the multiplication does after loading the bases (`tail`): `[o] < m` and
`[o] 2^(64 w) ≡ [a] [b] (mod m)`, with only arrays 2, 3 and `o` changed. The
code sets the rounds' count itself, and computes `-m⁻¹ mod 2⁶⁴` from any
`r12` that `hinv` holds of: the hypotheses on `r4` and on the size of `r12`
(`_i4`, `_i12`) are those its callers prove. -/
theorem tailW_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
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
        Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * w), (slot w o, 8 * (w + 2))] s.mem t.mem) ∧
      Keep tailRegs s t := by
  have h := tailWith_ok rounds_spec hs hn ho ha hb ho2 ho3 ha2 hb2 hw2 hw' hZ i5 i6 i7 i8 i9 i10 i11 _i4 _i12 hinv hB
  have h₁ := WP.gpr h (r := .r21) (by unfold zeroAcc rounds subMod64M selectAcc64; decide +kernel)
  have h₂ := WP.gpr h₁ (r := .r28) (by unfold zeroAcc rounds subMod64M selectAcc64; decide +kernel)
  have h₃ := WP.gpr h₂ (r := .r29) (by unfold zeroAcc rounds subMod64M selectAcc64; decide +kernel)
  have h₄ := WP.gpr h₃ (r := .r30) (by unfold zeroAcc rounds subMod64M selectAcc64; decide +kernel)
  have h₅ := WP.gpr h₄ (r := .r31) (by unfold zeroAcc rounds subMod64M selectAcc64; decide +kernel)
  refine WP.mono h₅ fun t ⟨⟨⟨⟨⟨⟨hp, k⟩, e21⟩, e28⟩, e29⟩, e30⟩, e31⟩ => ⟨hp, fun r hr => ?_, k.rd, k.wr, k.sp, k.lr⟩
  by_cases hr' : r ∈ tailRegs8
  · simp only [tailRegs8, tailRegs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr' hr
    rcases hr' with hr' | hr'
    · exact absurd hr' hr
    · rcases hr' with rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact k.gpr r hr'

/-- `tailW_ok`, of the kernel's `tail8`, which also writes `r21` and `r28`–`r31`. -/
theorem tail8W_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {n o a b : Nat} (hn : 4 ≤ n) (ho : o < n) (ha : a < n) (hb : b < n) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2)
    (hb2 : b ≠ 2) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w n ≤ Z)
    (i5 : s.gpr .r5 = off B (slot w o)) (i6 : s.gpr .r6 = off B (slot w a))
    (i7 : s.gpr .r7 = off B (slot w b)) (i8 : s.gpr .r8 = off B (slot w 2))
    (i9 : s.gpr .r9 = off B (slot w 3)) (i10 : s.gpr .r10 = off B (slot w 0))
    (i11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (_i4 : s.gpr .r4 = BitVec.ofNat 64 (2 * w))
    (_i12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem B (slot w b) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa tail8 s fun t =>
      (val32 t.mem B (slot w o) (2 * w) < val32 s.mem B (slot w 0) (2 * w) ∧
        val32 t.mem B (slot w o) (2 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          val32 s.mem B (slot w a) (2 * w) * val32 s.mem B (slot w b) (2 * w) %
            val32 s.mem B (slot w 0) (2 * w) ∧
        Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * w), (slot w o, 8 * (w + 2))] s.mem t.mem) ∧
      Keep tailRegs8 s t := by
  unfold tail8
  exact tailWith_ok rounds8_spec hs hn ho ha hb ho2 ho3 ha2 hb2 hw2 hw' hZ i5 i6 i7 i8 i9 i10 i11 _i4 _i12 hinv hB

/-- `tailW_ok` with all of the temporary changed. -/
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
      Keep tailRegs s t :=
  WP.mono (tailW_ok hs hn ho ha hb ho2 ho3 ha2 hb2 hw2 hw' hZ i5 i6 i7 i8 i9 i10 i11 _i4 _i12 hinv hB) fun t ⟨⟨h1, h2, h3⟩, k⟩ => ⟨⟨h1, h2, Outs.cover h3 fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Nat.le_refl _, by omega_arith⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Nat.le_refl _,
        Nat.le_refl _⟩⟩, k⟩

theorem shl2_ofNat (w : Nat) : BitVec.ofNat 64 (2 * w) <<< 2 = BitVec.ofNat 64 (8 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- The registers the kernel's body writes. -/
def kernelRegs8 : List Reg := .r11 :: .r12 :: tailRegs8

/-! ## The vector registers the kernel keeps callers' registers in -/

/-- Whether an instruction may write a vector register. -/
def vWrites : Instr → Bool
  | .vop .. | .lxvd2x .. | .lxvd2xTbl .. | .mtvsrd .. => true
  | _ => false

theorem exec_vpr {i : Instr} {s s' : State} (hi : vWrites i = false) (h : exec i s = some s') : s'.vpr = s.vpr := by
  have hst : ∀ {a : Addr} {n : Nat} {v : BitVec (8 * n)}, s.store a n v = some s' → s'.vpr = s.vpr := by
    intro a n v h
    simp only [State.store] at h
    split at h <;> cases h; rfl
  cases i with
  | store sz t n off | stb t n off | stxvd2x t n off =>
    simp only [reduceExec, Option.bind_eq_some_iff] at h
    obtain ⟨a, -, h⟩ := h
    exact hst h
  | storeRev sz t a b =>
    cases sz <;>
    · simp only [reduceExec, Option.bind_eq_some_iff] at h
      obtain ⟨a, -, h⟩ := h
      exact hst h
  | load sz t n off | lbz t n off =>
    simp only [reduceExec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h
    rfl
  | loadRev sz t a b =>
    cases sz <;>
    · simp only [reduceExec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, -, v, -, rfl⟩ := h
      rfl
  | vop _ | lxvd2x _ _ _ | lxvd2xTbl _ _ _ _ _ | mtvsrd _ _ => simp [vWrites] at hi
  | push _ | pop _ | alloc _ | free _ | bctrl => simp only [reduceExec, reduceCtorEq] at h
  | _ =>
    simp only [reduceExec] at h
    first
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | (split at h <;> [skip; cases h]
       simp only [Option.some.injEq] at h; subst h; rfl)

theorem execBlock_vpr {is : List Instr} (hc : ∀ i ∈ is, vWrites i = false)
    {s s' : State} {t : List Leak} (h : execBlock isa is s = some (s', t)) : s'.vpr = s.vpr := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) h2, exec_vpr (hc i (List.mem_cons_self ..)) he]

/-- Code that calls nothing and writes no vector register keeps the vector
registers. -/
theorem Exec.vpr {c : Prog isa} (hc : ∀ i ∈ instrs c, vWrites i = false) (hn : c.noCalls = true)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') : s'.vpr = s.vpr := by
  induction h with
  | block h => exact execBlock_vpr hc h
  | seq _ _ ih₁ ih₂ =>
    simp only [Code.noCalls, Bool.and_eq_true] at hn
    rw [ih₂ (fun i hi => hc i (List.mem_append_right _ hi)) hn.2, ih₁ (fun i hi => hc i (List.mem_append_left _ hi)) hn.1]
  | iteT _ _ ih =>
    simp only [Code.noCalls, Bool.and_eq_true] at hn
    exact ih (fun i hi => hc i (List.mem_append_left _ hi)) hn.1
  | iteF _ _ ih =>
    simp only [Code.noCalls, Bool.and_eq_true] at hn
    exact ih (fun i hi => hc i (List.mem_append_right _ hi)) hn.2
  | loopExit _ _ ih => exact ih hc hn
  | loopNext _ _ _ ih₁ ih₂ => rw [ih₂ hc hn, ih₁ hc hn]
  | call | frame | icall | icallNext => simp [Code.noCalls] at hn

theorem WP.vpr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q)
    (hc : ∀ i ∈ instrs c, vWrites i = false) (hn : c.noCalls = true) :
    WP isa c s fun s' => Q s' ∧ s'.vpr = s.vpr := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.vpr hc hn he⟩

theorem vdword_append (a b : BitVec 64) : vdword (a ++ b) 0 = a :=
  show (a ++ b).extractLsb' 64 64 = a from BitVec.extractLsb'_append_eq_left

theorem mtvsrd_eq (s : State) (d : VReg) (n : Reg) :
    exec (.mtvsrd d n) s = some { s.writeV d (s.gpr n ++ s.unknowns 0) with unknowns := fun i => s.unknowns (i + 1) } := by
  simp only [reduceExec]

theorem mfvsrd_eq (s : State) (d : Reg) (n : VReg) : exec (.mfvsrd d n) s = some (s.write d (vdword (s.vpr n) 0)) := by
  simp only [reduceExec]

/-- `mtvsrd`: no register written, and `n` in the high half of `d`. -/
theorem wp_mtvsrd {is : List Instr} {s : State} {Q : State → Prop} (d : VReg) (n : Reg)
    (k : ∀ u, Keep [] s u → u.mem = s.mem → vdword (u.vpr d) 0 = s.gpr n → (∀ d', d' ≠ d → u.vpr d' = s.vpr d') →
      WP isa (.block is) u Q) :
    WP isa (.block (.mtvsrd d n :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨_, mtvsrd_eq s d n, k _ ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩ rfl
    (by simp only [State.writeV, ite_true]; exact vdword_append _ _)
    fun d' hd => by simp only [State.writeV, ite_eq_right_iff]; exact fun e => absurd e hd⟩

/-- `kernelSave`: no register written, and each saved register in the high
half of its vector register. -/
theorem kernelSave_ok (s : State) :
    WP isa (.block kernelSave) s fun u => Keep [] s u ∧ u.mem = s.mem ∧
      ∀ p ∈ kernelSaved, vdword (u.vpr p.1) 0 = s.gpr p.2 := by
  unfold kernelSave kernelSaved
  simp only [List.map_cons, List.map_nil]
  refine wp_mtvsrd .v0 .r21 fun u₁ k₁ m₁ e₁ f₁ => ?_
  refine wp_mtvsrd .v1 .r28 fun u₂ k₂ m₂ e₂ f₂ => ?_
  refine wp_mtvsrd .v2 .r29 fun u₃ k₃ m₃ e₃ f₃ => ?_
  refine wp_mtvsrd .v3 .r30 fun u₄ k₄ m₄ e₄ f₄ => ?_
  refine wp_mtvsrd .v4 .r31 fun u₅ k₅ m₅ e₅ f₅ => WP.block_nil ?_
  have g : ∀ r, u₄.gpr r = s.gpr r := fun r => by
    rw [k₄.gpr r (by simp), k₃.gpr r (by simp), k₂.gpr r (by simp), k₁.gpr r (by simp)]
  refine ⟨(((k₁.trans k₂).trans k₃).trans k₄).trans k₅ |>.mono (by simp), by rw [m₅, m₄, m₃, m₂, m₁], ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [f₅ _ (by decide), f₄ _ (by decide), f₃ _ (by decide), f₂ _ (by decide), e₁]
  · rw [f₅ _ (by decide), f₄ _ (by decide), f₃ _ (by decide), e₂, k₁.gpr _ (by simp)]
  · rw [f₅ _ (by decide), f₄ _ (by decide), e₃, k₂.gpr _ (by simp), k₁.gpr _ (by simp)]
  · rw [f₅ _ (by decide), e₄, k₃.gpr _ (by simp), k₂.gpr _ (by simp), k₁.gpr _ (by simp)]
  · rw [e₅, g]

/-- `kernelRestore`: each saved register from the high half of its vector
register, and no other register written. -/
theorem kernelRestore_ok (s : State) :
    WP isa (.block kernelRestore) s fun t => Keep (kernelSaved.map (·.2)) s t ∧ t.mem = s.mem ∧
      ∀ p ∈ kernelSaved, t.gpr p.2 = vdword (s.vpr p.1) 0 := by
  unfold kernelRestore kernelSaved
  simp only [List.map_cons, List.map_nil]
  refine WP.block_cons_iff.mpr ⟨_, mfvsrd_eq _ _ _, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, mfvsrd_eq _ _ _, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, mfvsrd_eq _ _ _, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, mfvsrd_eq _ _ _, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, mfvsrd_eq _ _ _, WP.block_nil ?_⟩
  refine ⟨⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, ite_eq_right hr.1, ite_eq_right hr.2.1, ite_eq_right hr.2.2.1, ite_eq_right hr.2.2.2.1,
      ite_eq_right hr.2.2.2.2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, gpr_write]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [reduceCtorEq, ite_true, ite_false] <;> rfl

theorem kernelRegs8_sub : ∀ r, r ∈ kernelRegs8 → r ∈ Reg.r11 :: .r12 :: tailRegs ∨ r ∈ kernelSaved.map (·.2) := by
  decide

/-- The registers the kernel writes. -/
def kernelRegs : List Reg := .r11 :: .r12 :: tailRegs

/-- The kernel's body (`kernelBody`): `tail8W_ok`, with `2 w` in `r4` and
`-m⁻¹ mod 2³²` in `r3` (`r11` and `r12` may hold anything), and `r14` kept
through the temporary's word `w + 1`; `r11` and `r12` are left holding `2 w`
and `-m⁻¹ mod 2³²`. -/
theorem kernelBody_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {n o a b : Nat} (hn : 4 ≤ n) (ho : o < n) (ha : a < n) (hb : b < n) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2)
    (hb2 : b ≠ 2) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w n ≤ Z)
    (i5 : s.gpr .r5 = off B (slot w o)) (i6 : s.gpr .r6 = off B (slot w a))
    (i7 : s.gpr .r7 = off B (slot w b)) (i8 : s.gpr .r8 = off B (slot w 2))
    (i9 : s.gpr .r9 = off B (slot w 3)) (i10 : s.gpr .r10 = off B (slot w 0))
    (i4 : s.gpr .r4 = BitVec.ofNat 64 (2 * w)) (i3 : (s.gpr .r3).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r3).toNat + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem B (slot w b) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa kernelBody s fun t =>
      (val32 t.mem B (slot w o) (2 * w) < val32 s.mem B (slot w 0) (2 * w) ∧
        val32 t.mem B (slot w o) (2 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          val32 s.mem B (slot w a) (2 * w) * val32 s.mem B (slot w b) (2 * w) %
            val32 s.mem B (slot w 0) (2 * w) ∧
        Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))] s.mem t.mem ∧
        t.gpr .r14 = s.gpr .r14 ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧ t.gpr .r12 = s.gpr .r3) ∧
      Keep kernelRegs8 s t := by
  have hnw := hs.nowrap
  have sl : ∀ j < n, slot w j + 8 * (w + 2) ≤ Z := fun j hj => by
    have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ n by omega_using [hj])
    rw [Nat.add_mul, Nat.one_mul] at this
    unfold slot at hZ ⊢; omega_using [this, hZ]
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  have s3 := sl 3 (by omega_arith)
  -- The temporary's word `w + 1`, where `r14` is kept.
  have hd : slot w 3 + 8 * w + 8 + 8 ≤ Z := by omega_arith
  have ap : ∀ j, j < n → j ≠ 3 → slot w j + 8 * (w + 2) ≤ slot w 3 ∨ slot w 3 + 8 * (w + 2) ≤ slot w j :=
    fun j _ hj => sp hj
  unfold kernelBody
  refine WP.seq (WP.mono (WP.keep [.r3, .r11, .r12] (Q := fun u => u.gpr .r12 = s.gpr .r3 ∧
      u.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧ u.mem = s.mem.writeW (off B (slot w 3 + 8 * w + 8)) (s.gpr .r14))
    (by
      unfold kernelEntry
      prun [i4, i9, shl2_ofNat w, off_add, BitVec.add_zero, hs.st (show slot w 3 + 8 * w + 8 + 8 ≤ Z from hd)])
    (by decide)) fun u ⟨⟨u12, u11, um⟩, ku⟩ => ?_)
  have ow : Outside B (slot w 3 + 8 * w + 8) 8 s.mem u.mem := by
    rw [um]; exact writeW_outside _ B _ (by omega_arith)
  have vu : ∀ j, j < n → val32 u.mem B (slot w j) (2 * w) = val32 s.mem B (slot w j) (2 * w) := fun j hj => by
    by_cases e : j = 3
    · subst e; exact Outside.val32 ow (by omega_arith) (by omega_arith)
    · exact Outside.val32 ow (by have := ap j hj e; omega_arith) (by have := sl j hj; omega_arith)
  have gu : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r14], u.gpr r = s.gpr r := fun r hr =>
    ku.gpr r (by revert r hr; decide)
  have w0 : w32 u.mem B (slot w 0) = w32 s.mem B (slot w 0) :=
    Outside.w32 ow (by have := ap 0 (by omega_arith) (by decide); omega_arith) (by have := sl 0 (by omega_arith); omega_arith)
  refine WP.seq (WP.mono (tail8W_ok (hs.congr ku.wr) hn ho ha hb ho2 ho3 ha2 hb2 hw2 hw' hZ
    ((gu .r5 (by decide)).trans i5) ((gu .r6 (by decide)).trans i6) ((gu .r7 (by decide)).trans i7)
    ((gu .r8 (by decide)).trans i8) ((gu .r9 (by decide)).trans i9) ((gu .r10 (by decide)).trans i10) u11
    ((gu .r4 (by decide)).trans i4) (by rw [u12]; exact i3) (by rw [u12, w0]; exact hinv)
    (by rw [vu b hb, vu 0 (by omega_arith)]; exact hB)) fun t ⟨⟨tlt, teq, tout⟩, kt⟩ => ?_)
  have gt : ∀ r ∈ [Reg.r9, .r11, .r12], t.gpr r = u.gpr r := fun r hr => kt.gpr r (by revert r hr; decide)
  have tw : Mont.word t.mem B (slot w 3 + 8 * w + 8) = s.gpr .r14 := by
    rw [Outs.word tout (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · have := sp (show (2 : Nat) ≠ 3 by decide); omega_arith
        · omega_arith
        · have := ap o ho ho3; omega_arith) (by omega_arith), um, VG.Proof.Mont.word_writeW_self]
  have hst : Scr t B Z := hs.congr (ku.trans kt).wr
  refine WP.mono (WP.keep [.r3, .r14] (Q := fun t' => t'.gpr .r14 = s.gpr .r14 ∧ t'.mem = t.mem) (by
      unfold kernelExit
      prun [gt .r11 (by decide), u11, gt .r9 (by decide), gu .r9 (by decide), i9, shl2_ofNat w, off_add,
        hst.ld (show slot w 3 + 8 * w + 8 + 8 ≤ Z from hd)]
      exact tw) (by decide)) fun t' ⟨⟨t14, tm⟩, kt'⟩ => ?_
  rw [vu a ha, vu b hb, vu 0 (by omega_arith)] at teq
  rw [vu 0 (by omega_arith)] at tlt
  refine ⟨⟨by rw [tm]; exact tlt, by rw [tm]; exact teq, ?_, t14, ?_, ?_⟩, ?_⟩
  · rw [tm]
    refine Outs.trans (Outs.of_outside (o := slot w 3) (n := 8 * (w + 2)) (Outside.mono ow (by omega_arith) (by omega_arith))
      (by simp)) (Outs.cover tout fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Nat.le_refl _, by omega_arith⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Nat.le_refl _,
        Nat.le_refl _⟩
  · rw [kt'.gpr .r11 (by decide), gt .r11 (by decide), u11]
  · rw [kt'.gpr .r12 (by decide), gt .r12 (by decide), u12]
  · exact ((ku.trans kt).trans kt').mono (by decide)

/-- The shared kernel (`kernel`), as `montOp` calls it: `kernelBody_ok`, and
`r21` and `r28`–`r31`, which the body writes, restored from the vector
registers that `kernelSave` kept them in. -/
theorem kernel_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {n o a b : Nat} (hn : 4 ≤ n) (ho : o < n) (ha : a < n) (hb : b < n) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2)
    (hb2 : b ≠ 2) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w n ≤ Z)
    (i5 : s.gpr .r5 = off B (slot w o)) (i6 : s.gpr .r6 = off B (slot w a))
    (i7 : s.gpr .r7 = off B (slot w b)) (i8 : s.gpr .r8 = off B (slot w 2))
    (i9 : s.gpr .r9 = off B (slot w 3)) (i10 : s.gpr .r10 = off B (slot w 0))
    (i4 : s.gpr .r4 = BitVec.ofNat 64 (2 * w)) (i3 : (s.gpr .r3).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r3).toNat + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem B (slot w b) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa kernel s fun t =>
      (val32 t.mem B (slot w o) (2 * w) < val32 s.mem B (slot w 0) (2 * w) ∧
        val32 t.mem B (slot w o) (2 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          val32 s.mem B (slot w a) (2 * w) * val32 s.mem B (slot w b) (2 * w) %
            val32 s.mem B (slot w 0) (2 * w) ∧
        Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))] s.mem t.mem ∧
        t.gpr .r14 = s.gpr .r14 ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧ t.gpr .r12 = s.gpr .r3) ∧
      Keep kernelRegs s t := by
  unfold kernel
  refine WP.seq (WP.mono (kernelSave_ok s) fun u ⟨ku, um, uv⟩ => ?_)
  have gu : ∀ r, u.gpr r = s.gpr r := fun r => ku.gpr r (by simp)
  have hb := WP.vpr (kernelBody_ok (hs.congr ku.wr) hn ho ha hb ho2 ho3 ha2 hb2 hw2 hw' hZ
      (by rw [gu]; exact i5) (by rw [gu]; exact i6) (by rw [gu]; exact i7) (by rw [gu]; exact i8)
      (by rw [gu]; exact i9) (by rw [gu]; exact i10) (by rw [gu]; exact i4) (by rw [gu]; exact i3)
      (by rw [um, gu]; exact hinv) (by rw [um]; exact hB))
    (by unfold kernelBody kernelEntry kernelExit tail8 zeroAcc rounds8 subMod64M selectAcc64; decide +kernel)
    (by unfold kernelBody kernelEntry kernelExit tail8 zeroAcc rounds8 subMod64M selectAcc64; decide +kernel)
  refine WP.seq (WP.mono hb fun t ⟨⟨⟨tlt, teq, tout, t14, t11, t12⟩, kt⟩, tv⟩ => ?_)
  refine WP.mono (kernelRestore_ok t) fun t' ⟨kt', tm, tg⟩ => ?_
  rw [um] at tlt teq tout
  refine ⟨⟨by rw [tm]; exact tlt, by rw [tm]; exact teq, by rw [tm]; exact tout,
    by rw [kt'.gpr _ (by decide), t14, gu], by rw [kt'.gpr _ (by decide), t11],
    by rw [kt'.gpr _ (by decide), t12, gu]⟩, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩⟩
  · by_cases hs' : r ∈ kernelSaved.map (·.2)
    · simp only [kernelSaved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hs'
      have e : ∀ p ∈ kernelSaved, t'.gpr p.2 = s.gpr p.2 := fun p hp => by
        rw [tg p hp, tv, uv p hp]
      rcases hs' with rfl | rfl | rfl | rfl | rfl
      · exact e (.v0, .r21) (by decide)
      · exact e (.v1, .r28) (by decide)
      · exact e (.v2, .r29) (by decide)
      · exact e (.v3, .r30) (by decide)
      · exact e (.v4, .r31) (by decide)
    · rw [kt'.gpr r hs', kt.gpr r (fun h => ((kernelRegs8_sub r h).elim hr hs')), gu]
  · rw [kt'.rd, kt.rd, ku.rd]
  · rw [kt'.wr, kt.wr, ku.wr]
  · rw [kt'.sp, kt.sp, ku.sp]
  · rw [kt'.lr, kt.lr, ku.lr]

end VG.Proof.Bignum.PPC64LE
