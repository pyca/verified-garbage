module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRounds
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRows
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
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontSqr
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

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

/-- The registers `tail` writes, with its rounds' blocks of eight words. -/
def tailRegs8 : List Reg := tailRegs ++ [.r27, .r28, .r29, .r30, .r31]

/-- The registers the kernel's `tail8` writes. -/
def tailRegsK : List Reg := tailRegs8 ++ [.r2, .r23, .r24, .r25, .r26]

theorem Outs.of_outside2 {base : Addr} {o n₁ n₂ : Nat} {rs : List (Nat × Nat)} {m m' : Mem}
    (h : Mont.Outside base o (n₁ + n₂) m m') (h₁ : (o, n₁) ∈ rs) (h₂ : (o + n₁, n₂) ∈ rs) : Outs base rs m m' :=
  fun x hx => h x (by have a1 := hx _ h₁; have a2 := hx _ h₂; simp only at a1 a2; omega_arith)

/-- The end of the multiplication (`subMod64M`, `selectAcc64`), after rounds or
the squaring that leave `T < 2 m` with `2^(64 w) T ≡ a b (mod m)` in the
accumulator (`w + 1` words), with only it and the temporary's first `w` words
changed, `m'` in `r22` and the bases where they were: `[o] < m` and `[o] 2^(64 w)
≡ a b (mod m)`. -/
theorem finishW_ok {out : List Reg} (hout : ∀ r ∈ tailRegs8, r ∈ out) {s s₃ : State} {B : Addr} {Z w : Nat}
    (hs : Scr s B Z) {n o a b : Nat} (hn : 4 ≤ n) (ho : o < n) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (hw2 : 2 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w n ≤ Z) (i5 : s.gpr .r5 = off B (slot w o)) (i8 : s.gpr .r8 = off B (slot w 2))
    (i9 : s.gpr .r9 = off B (slot w 3)) (i10 : s.gpr .r10 = off B (slot w 0))
    (i11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (_i12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (tlt : wordsVal s₃.mem B (slot w 2) (w + 1) < 2 * wordsVal s.mem B (slot w 0) w)
    (teq : 2 ^ (64 * w) * wordsVal s₃.mem B (slot w 2) (w + 1) % wordsVal s.mem B (slot w 0) w =
      wordsVal s.mem B (slot w a) w * wordsVal s.mem B (slot w b) w % wordsVal s.mem B (slot w 0) w)
    (out₃ : Mont.Outside B (slot w 2) (8 * (w + 2) + 8 * w) s.mem s₃.mem)
    (r22 : s₃.gpr .r22 = (Mont.word s.mem B (slot w 0) * s.gpr .r12 + BitVec.ofNat 64 2) * s.gpr .r12)
    (g : ∀ r ∈ [Reg.r5, .r8, .r9, .r10, .r11], s₃.gpr r = s.gpr r) (K : Keep (.r12 :: out) s s₃) :
    WP isa (.seq subMod64M selectAcc64) s₃ fun t =>
      (val32 t.mem B (slot w o) (2 * w) < val32 s.mem B (slot w 0) (2 * w) ∧
        val32 t.mem B (slot w o) (2 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          val32 s.mem B (slot w a) (2 * w) * val32 s.mem B (slot w b) (2 * w) %
            val32 s.mem B (slot w 0) (2 * w) ∧
        Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * w), (slot w o, 8 * (w + 2))] s.mem t.mem) ∧
      Keep out s t := by
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
  have so := sl o ho
  have p20 := sp (show (2 : Nat) ≠ 0 by decide)
  have p30 := sp (show (3 : Nat) ≠ 0 by decide)
  have p2o := sp (Ne.symm ho2)
  have p3o := sp (Ne.symm ho3)
  have e23 : slot w 3 = slot w 2 + 8 * (w + 2) := by unfold slot; omega_arith
  have hM := val32_lt s.mem B (slot w 0) (2 * w)
  have hinv' : ((Mont.word s.mem B (slot w 0)).toNat % 2 ^ 32 * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0 := by
    rw [w32_eq_mod] at hinv; exact hinv
  have wv : ∀ (m : Mem) (j : Nat), wordsVal m B (slot w j) w = val32 m B (slot w j) (2 * w) :=
    fun m j => wordsVal_eq_val32 m B _ w
  -- `r12` back, at the start of `T - m`.
  show WP isa (.seq (.seq (.block (restoreMinv ++ _)) _) _) s₃ _
  rw [WP.seq_iff, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = s.gpr .r12 ∧ t.mem = s₃.mem) (by
      unfold restoreMinv; prun [r22, minv_restore _ _ _i12 hinv']) (by decide)) fun s₄ ⟨⟨r12₄, m₄⟩, k₄⟩ => ?_
  rw [← WP.seq_iff, ← WP.seq_iff]
  rw [← m₄] at tlt teq out₃
  rw [wordsVal_succ_top] at tlt teq
  have hs₄ := hs.congr (K.trans k₄).wr
  have g₄ : ∀ r ∈ [Reg.r5, .r8, .r9, .r10, .r11], s₄.gpr r = s.gpr r := fun r hr => by
    rw [k₄.gpr r (by revert r hr; decide), g r hr]
  have m0 : wordsVal s₄.mem B (slot w 0) w = wordsVal s.mem B (slot w 0) w :=
    out₃.wordsVal (by omega_arith) (by omega_arith)
  -- `T - m`.
  refine WP.seq (WP.mono (subMod64_ok (w := w) (dA := slot w 2) (dT := slot w 3) (dM := slot w 0) hs₄
    (by rw [g₄ .r8 (by decide), i8]) (by rw [g₄ .r9 (by decide), i9]) (by rw [g₄ .r10 (by decide), i10])
    (by rw [g₄ .r11 (by decide), i11]) (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith))
    fun s₅ ⟨⟨c, hc, hD, h20⟩, out₅, k₅⟩ => ?_)
  rw [m0] at hD
  have hs₅ := hs₄.congr k₅.wr
  have g₅ : ∀ r ∈ [Reg.r5, .r8, .r9, .r11], s₅.gpr r = s.gpr r := fun r hr => by
    rw [k₅.gpr r (by revert r hr; decide), g₄ r (by revert r hr; decide)]
  have accA : wordsVal s₅.mem B (slot w 2) w = wordsVal s₄.mem B (slot w 2) w :=
    out₅.wordsVal (by omega_arith) (by omega_arith)
  -- The selection.
  refine WP.mono (selectAcc64_ok (w := w) (dA := slot w 2) (dT := slot w 3) (dO := slot w o)
    (b := decide ((Mont.word s₄.mem B (slot w 2 + 8 * w)).toNat < c)) hs₅
    (by rw [g₅ .r8 (by decide), i8]) (by rw [g₅ .r9 (by decide), i9]) (by rw [g₅ .r5 (by decide), i5])
    (by rw [g₅ .r11 (by decide), i11]) (by rw [h20]; simp only [decide_eq_true_eq]) (by omega_arith) hw'
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨hv, out₆, k₆⟩ => ?_
  rw [accA] at hv
  have hM' := wordsVal_lt s.mem B (slot w 0) w
  have hM0 : 0 < wordsVal s.mem B (slot w 0) w := by omega_arith
  have hres : wordsVal t.mem B (slot w o) w =
      (wordsVal s₄.mem B (slot w 2) w + 2 ^ (64 * w) * ((Mont.word s₄.mem B (slot w 2 + 8 * w)).toNat +
        2 ^ 64 * 0)) % wordsVal s.mem B (slot w 0) w := by
    rw [hv, ← VG.Proof.Bignum.csub_result hM' (wordsVal_lt _ _ _ _) hc (wordsVal_lt _ _ _ _)
      (by rw [Nat.mul_zero, Nat.add_zero]; exact tlt) hD]
    by_cases h : (Mont.word s₄.mem B (slot w 2 + 8 * w)).toNat < c <;> simp [h]
  rw [Nat.mul_zero, Nat.add_zero] at hres
  rw [← wv, ← wv, ← wv, ← wv]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hres]; exact Nat.mod_lt _ hM0
  · rw [hres, Nat.mod_mul_mod, Nat.mul_comm, teq]
  · refine Outs.trans (Outs.of_outside2 (o := slot w 2) (n₁ := 8 * (w + 2)) (n₂ := 8 * w) out₃ (by simp)
      (by rw [← e23]; simp)) ?_
    refine Outs.trans (Outs.of_outside (o := slot w 3) (n := 8 * w) out₅ (by simp)) ?_
    exact Outs.of_outside (o := slot w o) (n := 8 * (w + 2)) (out₆.mono (Nat.le_refl _) (by omega_arith)) (by simp)
  · have K₂ : Keep (.r12 :: tailRegs8) s₄ t := (k₅.trans k₆).mono (by decide)
    have m8 : ∀ {r}, r ∈ Reg.r12 :: tailRegs8 → r ∈ Reg.r12 :: out := fun h =>
      (List.mem_cons.mp h).elim (fun e => e ▸ List.mem_cons_self ..) fun h => List.mem_cons_of_mem _ (hout _ h)
    have K' : Keep (.r12 :: out) s t := ((K.trans k₄).trans K₂).mono fun r hr => by
      rcases List.mem_append.mp hr with h | h
      · rcases List.mem_append.mp h with h | h
        · exact h
        · rw [List.mem_singleton] at h; subst h; exact List.mem_cons_self ..
      · exact m8 h
    have t12 : t.gpr .r12 = s.gpr .r12 := by
      rw [k₆.gpr .r12 (by decide), k₅.gpr .r12 (by decide), r12₄]
    refine ⟨fun r hr => ?_, K'.rd, K'.wr, K'.sp, K'.lr⟩
    by_cases e : r = .r12
    · subst e; exact t12
    · exact K'.gpr r (by simp only [List.mem_cons, not_or]; exact ⟨e, hr⟩)

/-- Everything the multiplication does after loading the bases, with any rounds
`R` that do what the rounds do (`RoundsSpecW`), writing at most `rr`: `[o] < m` and
`[o] 2^(64 w) ≡ [a] [b] (mod m)`, with only arrays 2, 3 and `o` changed. The
code sets the rounds' count itself, and computes `-m⁻¹ mod 2⁶⁴` from any
`r12` that `hinv` holds of: the hypothesis on the size of `r12` (`_i12`) is the
one its callers prove. -/
theorem tailWith_ok {R : Prog isa} {rr out : List Reg} (hR : RoundsSpecW rr R)
    (hk : ∀ r ∈ [Reg.r5, .r8, .r9, .r10, .r11], r ∉ rr) (hrr : ∀ r ∈ rr, r ∈ .r12 :: out)
    (hout : ∀ r ∈ tailRegs8, r ∈ out) {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {n o a b : Nat} (hn : 4 ≤ n) (ho : o < n) (ha : a < n) (hb : b < n) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2)
    (hb2 : b ≠ 2) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w n ≤ Z)
    (i5 : s.gpr .r5 = off B (slot w o)) (i6 : s.gpr .r6 = off B (slot w a))
    (i7 : s.gpr .r7 = off B (slot w b)) (i8 : s.gpr .r8 = off B (slot w 2))
    (i9 : s.gpr .r9 = off B (slot w 3)) (i10 : s.gpr .r10 = off B (slot w 0))
    (i11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (_i12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem B (slot w b) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa (.seq zeroAcc (.seq R (.seq subMod64M selectAcc64))) s fun t =>
      (val32 t.mem B (slot w o) (2 * w) < val32 s.mem B (slot w 0) (2 * w) ∧
        val32 t.mem B (slot w o) (2 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          val32 s.mem B (slot w a) (2 * w) * val32 s.mem B (slot w b) (2 * w) %
            val32 s.mem B (slot w 0) (2 * w) ∧
        Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * w), (slot w o, 8 * (w + 2))] s.mem t.mem) ∧
      Keep out s t := by
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
  have p20 := sp (show (2 : Nat) ≠ 0 by decide)
  have p23 := sp (show (2 : Nat) ≠ 3 by decide)
  have p2a := sp (Ne.symm ha2)
  have p2b := sp (Ne.symm hb2)
  have hinv' : ((Mont.word s.mem B (slot w 0)).toNat % 2 ^ 32 * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0 := by
    rw [w32_eq_mod] at hinv; exact hinv
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
  have e22 : s₂'.gpr .r22 = (Mont.word s.mem B (slot w 0) * s.gpr .r12 + BitVec.ofNat 64 2) * s.gpr .r12 := e22'
  -- The rounds.
  refine WP.seq (WP.mono (hR (w := w) (da := slot w a) (dA := slot w 2) (dB := slot w b) (dM := slot w 0) hs₂'
    (by rw [g₂' .r6 (by decide), i6]) (by rw [g₂' .r8 (by decide), i8]) (by rw [g₂' .r7 (by decide), i7])
    (by rw [g₂' .r9 (by decide), i9, show slot w 2 + 8 * (w + 2) = slot w 3 by unfold slot; omega_arith])
    (by rw [g₂' .r10 (by decide), i10]) (by rw [g₂' .r11 (by decide), i11]) j4
    (by rw [m0₂, e22]; exact mont_newton64 _ _ hinv') w22.symm hw2 hw' (by unfold slot; omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) hz
    (by rw [v₂ hb hb2, v₂ (by omega_using [hn]) (by decide), wv, wv]; exact hB))
    fun s₃' ⟨⟨tlt, teq, out₃, r22₃⟩, k₃'⟩ => ?_)
  rw [v₂ (by omega_using [hn]) (by decide)] at tlt teq
  rw [v₂ ha ha2, v₂ hb hb2] at teq
  refine finishW_ok hout hs hn ho ho2 ho3 hw2 hw' hZ i5 i8 i9 i10 i11 _i12 hinv tlt teq
    ((out₂.trans out₃).mono (Nat.le_refl _) (by omega_arith)) (by rw [r22₃, e22])
    (fun r hr => by rw [k₃'.gpr r (hk r hr), g₂' r (by revert r hr; decide)]) ?_
  have K₁ : Keep (.r12 :: tailRegs8) s s₂' := k₂'.mono (by decide)
  have m8 : ∀ {r}, r ∈ Reg.r12 :: tailRegs8 → r ∈ Reg.r12 :: out := fun h =>
    (List.mem_cons.mp h).elim (fun e => e ▸ List.mem_cons_self ..) fun h => List.mem_cons_of_mem _ (hout _ h)
  exact (K₁.trans k₃').mono fun r hr => by
    rcases List.mem_append.mp hr with h | h
    exacts [m8 h, hrr r h]


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
  have h := tailWith_ok rounds_spec (by decide) (by decide) (fun _ h => h) hs hn ho ha hb ho2 ho3 ha2 hb2 hw2 hw' hZ i5 i6 i7 i8 i9 i10 i11 _i12 hinv hB
  have h₁ := WP.gpr h (r := .r27) (by unfold zeroAcc rounds subMod64M selectAcc64; decide +kernel)
  have h₂ := WP.gpr h₁ (r := .r28) (by unfold zeroAcc rounds subMod64M selectAcc64; decide +kernel)
  have h₃ := WP.gpr h₂ (r := .r29) (by unfold zeroAcc rounds subMod64M selectAcc64; decide +kernel)
  have h₄ := WP.gpr h₃ (r := .r30) (by unfold zeroAcc rounds subMod64M selectAcc64; decide +kernel)
  have h₅ := WP.gpr h₄ (r := .r31) (by unfold zeroAcc rounds subMod64M selectAcc64; decide +kernel)
  refine WP.mono h₅ fun t ⟨⟨⟨⟨⟨⟨hp, k⟩, e21⟩, e28⟩, e29⟩, e30⟩, e31⟩ => ⟨hp, fun r hr => ?_, k.rd, k.wr, k.sp, k.lr⟩
  by_cases hr' : r ∈ tailRegs8
  · simp only [tailRegs8, tailRegs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr' hr
    rcases hr' with hr' | hr'
    · exact absurd hr' hr
    · rcases hr' with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · exact k.gpr r hr'

theorem off_inj {B : Addr} {x y : Nat} (hx : B.toNat + x < 2 ^ 64) (hy : B.toNat + y < 2 ^ 64)
    (h : off B x = off B y) : x = y := by
  have := congrArg BitVec.toNat h
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega_arith

theorem slot_inj {w j k : Nat} (h : slot w j = slot w k) : j = k := by
  unfold slot at h
  exact Nat.eq_of_mul_eq_mul_right (by omega_arith : 0 < 8 * (w + 2)) (by omega_arith)

/-- `tailW_ok`, of the kernel's `tail8`, which also writes `r2` and `r23`–`r31`,
and squares (`sqr8`) when `a` and `b` are the same array, not the temporary,
and `w` is a multiple of 8. -/
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
      Keep tailRegsK s t := by
  have hnw := hs.nowrap
  have sl : ∀ j < n, slot w j + 8 * (w + 2) ≤ Z := fun j hj => by
    have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ n by omega_using [hj])
    rw [Nat.add_mul, Nat.one_mul] at this
    unfold slot at hZ ⊢; omega_using [this, hZ]
  unfold tail8
  refine WP.seq (WP.mono (Sqr.sqrFlag_ok i11) fun u ⟨hf, mu, _, ku⟩ => ?_)
  have gu : ∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], u.gpr r = s.gpr r := fun r hr =>
    ku.gpr r (by revert r hr; decide)
  have hsu : Scr u B Z := hs.congr ku.wr
  -- The squaring also writes `r7` to `r10`, but leaves them as it found them.
  have sqrRegs_sub : ∀ r ∈ ([.r0, .r3, .r4, .r30] : List Reg) ++ Sqr.sqrRegs,
      r ∈ Reg.r12 :: tailRegsK ∨ r ∈ ([.r7, .r8, .r9, .r10] : List Reg) := by decide
  refine WP.ite _ (VG.PPC64LE.eval_zero u .r3) (fun hz => ?_) (fun hz => ?_)
  · -- The squaring.
    obtain ⟨e67, hw8, n69⟩ := hf (by simpa using hz)
    have sa := sl a ha
    have sb := sl b hb
    have s3 := sl 3 (by omega_arith)
    have hxa : B.toNat + slot w a < 2 ^ 64 := by omega_using [hnw, sa]
    have hxb : B.toNat + slot w b < 2 ^ 64 := by omega_using [hnw, sb]
    have hab : a = b := slot_inj (off_inj hxa hxb (by rw [← i6, ← i7]; exact e67))
    subst hab
    have ha3 : a ≠ 3 := fun h => n69 (by rw [i6, i9, h])
    obtain ⟨K, rfl⟩ : ∃ K, w = 8 * K := ⟨w / 8, by omega_arith⟩
    have p2a := slot_sep (w := 8 * K) (Ne.symm ha2)
    have p3a := slot_sep (w := 8 * K) (Ne.symm ha3)
    have e23 : slot (8 * K) 3 = slot (8 * K) 2 + 8 * (8 * K + 2) := by unfold slot; omega_arith
    have e20 : slot (8 * K) 2 = slot (8 * K) 0 + 16 * (8 * K + 2) := by unfold slot; omega_arith
    have hinv' : ((Mont.word s.mem B (slot (8 * K) 0)).toNat % 2 ^ 32 * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0 := by
      rw [w32_eq_mod] at hinv; exact hinv
    have wv : ∀ (m : Mem) (j : Nat), wordsVal m B (slot (8 * K) j) (8 * K) = val32 m B (slot (8 * K) j) (2 * (8 * K)) :=
      fun m j => wordsVal_eq_val32 m B _ _
    rw [WP.seq_iff]
    refine WP.mono (Sqr.sqr8_ok (da := slot (8 * K) a) (dS := slot (8 * K) 2) (dM := slot (8 * K) 0) (K := K) hsu
      (by rw [gu .r6 (by decide), i6]) (by rw [gu .r8 (by decide), i8]) (by rw [gu .r10 (by decide), i10])
      (by rw [gu .r11 (by decide), i11]) (by omega_arith) (by omega_arith) e20 (by omega_arith) (by omega_arith)
      (by omega_arith) (by rw [mu, gu .r12 (by decide)]; exact mont_newton64 _ _ hinv')
      (by rw [mu, wv, wv]; exact hB)) fun s₃ ⟨⟨tlt, teq, out, r22, r8, r9, r10, r7⟩, k⟩ => ?_
    rw [mu] at tlt teq out
    refine finishW_ok (out := tailRegsK) (fun r h => by simp [tailRegsK, h]) hs hn ho ho2 ho3 hw2 hw' hZ i5 i8 i9 i10 i11
      _i12 hinv (by rwa [show 8 * K + 1 = 8 * K + 1 from rfl] at tlt) teq
      (out.mono (Nat.le_refl _) (by omega_arith)) (by rw [r22, mu, gu .r12 (by decide)]) (fun r hr => ?_) ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [k.gpr _ (by decide), gu .r5 (by decide)]
      · rw [r8, gu .r8 (by decide)]
      · rw [r9, ← e23, i9]
      · rw [r10, gu .r10 (by decide)]
      · rw [k.gpr _ (by decide), gu .r11 (by decide)]
    · have K' := ku.trans k
      refine ⟨fun r hr => ?_, K'.rd, K'.wr, K'.sp, K'.lr⟩
      by_cases h7 : r ∈ ([.r7, .r8, .r9, .r10] : List Reg)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h7
        rcases h7 with rfl | rfl | rfl | rfl
        · rw [r7, gu .r6 (by decide), e67]
        · rw [r8, gu .r8 (by decide)]
        · rw [r9, ← e23, i9]
        · rw [r10, gu .r10 (by decide)]
      · exact K'.gpr r fun h => (sqrRegs_sub r h).elim hr h7
  · -- The rounds.
    refine WP.mono (tailWith_ok (out := tailRegsK) roundsK_spec (by decide) (by decide) (fun r h => by simp [tailRegsK, h]) hsu hn ho ha hb
      ho2 ho3 ha2 hb2 hw2 hw' hZ (by rw [gu .r5 (by decide), i5]) (by rw [gu .r6 (by decide), i6])
      (by rw [gu .r7 (by decide), i7]) (by rw [gu .r8 (by decide), i8]) (by rw [gu .r9 (by decide), i9])
      (by rw [gu .r10 (by decide), i10]) (by rw [gu .r11 (by decide), i11]) (by rw [gu .r12 (by decide)]; exact _i12)
      (by rw [mu, gu .r12 (by decide)]; exact hinv) (by rw [mu]; exact hB)) fun t ⟨h, k⟩ => ⟨by rwa [mu] at h,
        (ku.trans k).mono fun r hr => by
          rcases List.mem_append.mp hr with h | h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl | rfl | rfl <;> decide
          · exact h⟩

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
def kernelRegs8 : List Reg := .r11 :: .r12 :: tailRegsK

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

/-- Registers into the high halves of vector registers, one `mtvsrd` each:
no register written, and each one in its vector register. -/
theorem saves_ok : ∀ (L : List (VReg × Reg)), (L.map (·.1)).Nodup → ∀ s : State,
    WP isa (.block (L.map fun (v, r) => .mtvsrd v r)) s fun u => Keep [] s u ∧ u.mem = s.mem ∧
      (∀ p ∈ L, vdword (u.vpr p.1) 0 = s.gpr p.2) ∧ ∀ v, v ∉ L.map (·.1) → u.vpr v = s.vpr v
  | [], _, s => WP.block_nil ⟨Keep.refl _ _, rfl, fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl⟩
  | (v, r) :: L, hL, s => by
    rw [List.map_cons, List.map_cons, List.nodup_cons] at *
    refine wp_mtvsrd v r fun u₁ k₁ m₁ e₁ f₁ => WP.mono (saves_ok L hL.2 u₁) fun u ⟨k, m, e, f⟩ =>
      ⟨k₁.trans k |>.mono (by simp), by rw [m, m₁], fun p hp => ?_, fun v' hv' => ?_⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · rw [f _ hL.1, e₁]
      · rw [e p hp, k₁.gpr _ (by simp)]
    · rw [List.mem_cons, not_or] at hv'
      rw [f _ hv'.2, f₁ _ hv'.1]

/-- Registers from the high halves of vector registers, one `mfvsrd` each: only
they written, each from its vector register. -/
theorem restores_ok : ∀ (L : List (VReg × Reg)), (L.map (·.2)).Nodup → ∀ s : State,
    WP isa (.block (L.map fun (v, r) => .mfvsrd r v)) s fun t => Keep (L.map (·.2)) s t ∧ t.mem = s.mem ∧
      (∀ p ∈ L, t.gpr p.2 = vdword (s.vpr p.1) 0) ∧ t.vpr = s.vpr
  | [], _, s => WP.block_nil ⟨Keep.refl _ _, rfl, fun _ h => absurd h List.not_mem_nil, rfl⟩
  | (v, r) :: L, hL, s => by
    rw [List.map_cons, List.map_cons, List.nodup_cons] at *
    refine WP.block_cons_iff.mpr ⟨_, mfvsrd_eq _ _ _, WP.mono (restores_ok L hL.2 _) fun t ⟨k, m, e, f⟩ =>
      ⟨((Mont4.W1.write s r _).keep.trans k).mono (by simp), m, fun p hp => ?_, f⟩⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [k.gpr _ hL.1, gpr_write, ite_eq_left rfl]
    · rw [e p hp]; rfl

/-- `kernelSave`: no register written, and each saved register in the high
half of its vector register. -/
theorem kernelSave_ok (s : State) :
    WP isa (.block kernelSave) s fun u => Keep [] s u ∧ u.mem = s.mem ∧
      ∀ p ∈ kernelSaved, vdword (u.vpr p.1) 0 = s.gpr p.2 :=
  WP.mono (saves_ok kernelSaved (by decide) s) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

/-- `kernelRestore`: each saved register from the high half of its vector
register, and no other register written. -/
theorem kernelRestore_ok (s : State) :
    WP isa (.block kernelRestore) s fun t => Keep (kernelSaved.map (·.2)) s t ∧ t.mem = s.mem ∧
      ∀ p ∈ kernelSaved, t.gpr p.2 = vdword (s.vpr p.1) 0 :=
  WP.mono (restores_ok kernelSaved (by decide) s) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

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
`r2` and `r23`–`r31`, which the body writes, restored from the vector
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
    (by unfold kernelBody kernelEntry kernelExit tail8 zeroAcc roundsK subMod64M selectAcc64; decide +kernel)
    (by unfold kernelBody kernelEntry kernelExit tail8 zeroAcc roundsK subMod64M selectAcc64; decide +kernel)
  refine WP.seq (WP.mono hb fun t ⟨⟨⟨tlt, teq, tout, t14, t11, t12⟩, kt⟩, tv⟩ => ?_)
  refine WP.mono (kernelRestore_ok t) fun t' ⟨kt', tm, tg⟩ => ?_
  rw [um] at tlt teq tout
  refine ⟨⟨by rw [tm]; exact tlt, by rw [tm]; exact teq, by rw [tm]; exact tout,
    by rw [kt'.gpr _ (by decide), t14, gu], by rw [kt'.gpr _ (by decide), t11],
    by rw [kt'.gpr _ (by decide), t12, gu]⟩, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩⟩
  · by_cases hs' : r ∈ kernelSaved.map (·.2)
    · have e : ∀ p ∈ kernelSaved, t'.gpr p.2 = s.gpr p.2 := fun p hp => by
        rw [tg p hp, tv, uv p hp]
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs'
      exact e p hp
    · rw [kt'.gpr r hs', kt.gpr r (fun h => ((kernelRegs8_sub r h).elim hr hs')), gu]
  · rw [kt'.rd, kt.rd, ku.rd]
  · rw [kt'.wr, kt.wr, ku.wr]
  · rw [kt'.sp, kt.sp, ku.sp]
  · rw [kt'.lr, kt.lr, ku.lr]

end VG.Proof.Bignum.PPC64LE
