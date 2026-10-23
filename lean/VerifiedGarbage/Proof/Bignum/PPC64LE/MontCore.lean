module

import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRounds
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE VG.Impl.Bignum

theorem idx_shift {x : BitVec 64} {o : Nat} (h : x.setWidth 32 = BitVec.ofNat 32 o) (ho : o < 8) :
    (x.setWidth 32 >>> 0).setWidth 64 <<< 3 = BitVec.ofNat 64 (8 * o) := by
  rw [BitVec.ushiftRight_zero, h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem shl1_ofNat (w : Nat) : BitVec.ofNat 64 w <<< 1 = BitVec.ofNat 64 (2 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- `args`: the addresses of the header words of `o`, `a` and `b`, less 64. -/
theorem args_ok {s : State} {B : Addr} (h3 : s.gpr .r3 = B) {o a b : Nat} (ho : o < 8) (ha : a < 8)
    (hb : b < 8) (h5 : (s.gpr .r5).setWidth 32 = BitVec.ofNat 32 o)
    (h6 : (s.gpr .r6).setWidth 32 = BitVec.ofNat 32 a)
    (h7 : (s.gpr .r7).setWidth 32 = BitVec.ofNat 32 b) :
    WP isa (.block args) s fun t =>
      (t.gpr .r5 = off B (8 * o) ∧ t.gpr .r6 = off B (8 * a) ∧ t.gpr .r7 = off B (8 * b) ∧
        t.mem = s.mem) ∧ Keep [.r5, .r6, .r7] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold args slotOf
  prun [h3, idx_shift h5 ho, idx_shift h6 ha, idx_shift h7 hb]

/-- The registers `loads` writes. -/
def basesRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

/-- `loads`: the arrays' bases from the header (word `8 + j` holds array `j`'s,
at `slot w j`), `n = 2 w` and the rounds' count, and the low half of `-m⁻¹`. -/
theorem loads_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (h3 : s.gpr .r3 = B)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (h5 : s.gpr .r5 = off B (8 * o)) (h6 : s.gpr .r6 = off B (8 * a)) (h7 : s.gpr .r7 = off B (8 * b))
    (hZ : 256 ≤ Z) (harr : ∀ j < 8, s.mem.readW (off B (8 * j + 64)) 64 = off B (slot w j))
    (hw : s.mem.readW (off B 48) 64 = BitVec.ofNat 64 w) :
    WP isa (.block loads) s fun t =>
      (t.gpr .r5 = off B (slot w o) ∧ t.gpr .r6 = off B (slot w a) ∧ t.gpr .r7 = off B (slot w b) ∧
        t.gpr .r8 = off B (slot w 2) ∧ t.gpr .r9 = off B (slot w 3) ∧ t.gpr .r10 = off B (slot w 0) ∧
        t.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧ t.gpr .r4 = BitVec.ofNat 64 (2 * w) ∧
        (t.gpr .r12).toNat = w32 s.mem B 56 ∧ t.mem = s.mem) ∧ Keep basesRegs s t := by
  refine WP.keep _ ?_ (by decide)
  have h80 : s.mem.readW (off B 80) 64 = off B (slot w 2) := harr 2 (by decide)
  have h88 : s.mem.readW (off B 88) 64 = off B (slot w 3) := harr 3 (by decide)
  have h64 : s.mem.readW (off B 64) 64 = off B (slot w 0) := harr 0 (by decide)
  unfold loads
  prun [h3, h5, h6, h7, hs.ld (show 8 * o + 64 + 8 ≤ Z by omega),
    hs.ld (show 8 * a + 64 + 8 ≤ Z by omega), hs.ld (show 8 * b + 64 + 8 ≤ Z by omega), sArr, sW, sMinv,
    Nat.reduceMul, Nat.reduceAdd, hs.ld (show 80 + 8 ≤ Z by omega), hs.ld (show 88 + 8 ≤ Z by omega),
    hs.ld (show 64 + 8 ≤ Z by omega), hs.ld (show 48 + 8 ≤ Z by omega), hs.ld (show 56 + 4 ≤ Z by omega),
    harr o ho, harr a ha, harr b hb, h80, h88, h64, hw, shl1_ofNat w, BitVec.add_zero, toNat_ext32]

/-- The registers the arithmetic writes: all the volatile ones but `r21`,
which keeps the scratch buffer's address. -/
def coreRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
    .r22]

/-- The registers `tail` writes. -/
def tailRegs : List Reg :=
  [.r0, .r3, .r4, .r6, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22]

/-- Everything `mul` does after loading the bases (`tail`): `[o] < m` and
`[o] 2^(64 w) ≡ [a] [b] (mod m)`, with only arrays 2, 3 and `o` changed. -/
theorem tail_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2)
    (hb2 : b ≠ 2) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (i5 : s.gpr .r5 = off B (slot w o)) (i6 : s.gpr .r6 = off B (slot w a))
    (i7 : s.gpr .r7 = off B (slot w b)) (i8 : s.gpr .r8 = off B (slot w 2))
    (i9 : s.gpr .r9 = off B (slot w 3)) (i10 : s.gpr .r10 = off B (slot w 0))
    (i11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (i4 : s.gpr .r4 = BitVec.ofNat 64 (2 * w))
    (i12 : (s.gpr .r12).toNat < 2 ^ 32)
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
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  have hdr56 : 56 + 4 ≤ slot w 2 := by have := hdr_lt_slot w 2 (i := 7) (by decide); omega
  have s0 := sl 0 (by decide)
  have s2 := sl 2 (by decide)
  have s3 := sl 3 (by decide)
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
  unfold tail
  -- The accumulator := 0.
  refine WP.seq (WP.mono (zeroAcc_ok hs i8 i11 hw' (by omega)) fun s₂ ⟨hz, out₂, k₂⟩ => ?_)
  have hs₂ := hs.congr k₂.wr
  have g₂ : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], s₂.gpr r = s.gpr r := fun r hr =>
    k₂.gpr r (by revert r hr; decide)
  have v₂ : ∀ {j}, j < 8 → j ≠ 2 → val32 s₂.mem B (slot w j) (2 * w) = val32 s.mem B (slot w j) (2 * w) :=
    fun hj hne => out₂.val32 (by have := sp hne; omega) (by have := sl _ hj; omega)
  have w0₂ : w32 s₂.mem B (slot w 0) = w32 s.mem B (slot w 0) := out₂.w32 (by omega) (by omega)
  -- The rounds.
  refine WP.seq (WP.mono (rounds_ok (n := 2 * w) (da := slot w a) (dA := slot w 2) (dB := slot w b) (dM := slot w 0) hs₂ (by rw [g₂ .r6 (by decide), i6])
    (by rw [g₂ .r8 (by decide), i8]) (by rw [g₂ .r7 (by decide), i7]) (by rw [g₂ .r10 (by decide), i10])
    (by rw [g₂ .r11 (by decide), i11]) (by rw [g₂ .r4 (by decide), i4])
    (by rw [g₂ .r12 (by decide)]; exact i12)
    (by rw [g₂ .r12 (by decide), w0₂]; exact hinv) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (val32_zero fun j hj => hz j (by omega))
    (by rw [v₂ hb hb2, v₂ (by decide) (by decide)]; exact hB))
    fun s₃ ⟨⟨tlt, teq, out₃⟩, k₃⟩ => ?_)
  rw [v₂ (by decide) (by decide)] at tlt teq
  rw [v₂ ha ha2, v₂ hb hb2] at teq
  have hs₃ := hs₂.congr k₃.wr
  have g₃ : ∀ r ∈ [Reg.r5, .r8, .r9, .r10, .r11], s₃.gpr r = s.gpr r := fun r hr => by
    rw [k₃.gpr r (by revert r hr; decide), g₂ r (by revert r hr; decide)]
  have v₃ : ∀ {j}, j < 8 → j ≠ 2 → val32 s₃.mem B (slot w j) (2 * w) = val32 s.mem B (slot w j) (2 * w) :=
    fun hj hne => (out₃.val32 (by have := sp hne; omega) (by have := sl _ hj; omega)).trans (v₂ hj hne)
  -- `T - m`.
  refine WP.seq (WP.mono (subMod_ok (n := 2 * w) (dA := slot w 2) (dT := slot w 3) (dM := slot w 0) hs₃ (by rw [g₃ .r8 (by decide), i8])
    (by rw [g₃ .r9 (by decide), i9]) (by rw [g₃ .r10 (by decide), i10]) (by rw [g₃ .r11 (by decide), i11])
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun s₄ ⟨⟨c, hc, hD, h20⟩, out₄, k₄⟩ => ?_)
  rw [v₃ (by decide) (by decide)] at hD
  have hs₄ := hs₃.congr k₄.wr
  have g₄ : ∀ r ∈ [Reg.r5, .r8, .r9, .r11], s₄.gpr r = s.gpr r := fun r hr => by
    rw [k₄.gpr r (by revert r hr; decide), g₃ r (by revert r hr; decide)]
  have accA : val32 s₄.mem B (slot w 2) (2 * w) = val32 s₃.mem B (slot w 2) (2 * w) :=
    out₄.val32 (by omega) (by omega)
  -- The selection.
  refine WP.mono (selectAcc_ok (n := 2 * w) (dA := slot w 2) (dT := slot w 3) (dO := slot w o) (b := decide (w32 s₃.mem B (slot w 2 + 4 * (2 * w)) < c)) hs₄
    (by rw [g₄ .r8 (by decide), i8]) (by rw [g₄ .r9 (by decide), i9]) (by rw [g₄ .r5 (by decide), i5])
    (by rw [g₄ .r11 (by decide), i11]) (by rw [h20]; simp only [decide_eq_true_eq])
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun t ⟨hv, out₅, k₅⟩ => ?_
  rw [accA] at hv
  have hM := val32_lt s.mem B (slot w 0) (2 * w)
  have hM0 : 0 < val32 s.mem B (slot w 0) (2 * w) := by omega
  have pw : 2 ^ (32 * (2 * w)) = 2 ^ (64 * w) := by rw [← Nat.mul_assoc]
  rw [val32_succ] at tlt teq
  have hres : val32 t.mem B (slot w o) (2 * w) =
      (val32 s₃.mem B (slot w 2) (2 * w) + 2 ^ (32 * (2 * w)) * (w32 s₃.mem B (slot w 2 + 4 * (2 * w)) +
        2 ^ 64 * 0)) % val32 s.mem B (slot w 0) (2 * w) := by
    rw [hv, ← VG.Proof.Bignum.csub_result hM (val32_lt _ _ _ _) hc (val32_lt _ _ _ _) (by omega) hD]
    by_cases h : w32 s₃.mem B (slot w 2 + 4 * (2 * w)) < c <;> simp [h]
  rw [Nat.mul_zero, Nat.add_zero] at hres
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hres]; exact Nat.mod_lt _ hM0
  · rw [hres, ← pw, Nat.mod_mul_mod, Nat.mul_comm, teq]
  · refine Outs.trans (Outs.of_outside (o := slot w 2) (n := 8 * (w + 2))
      (out₂.mono (Nat.le_refl _) (by omega)) (by simp)) ?_
    refine Outs.trans (Outs.of_outside (o := slot w 2) (n := 8 * (w + 2))
      (out₃.mono (Nat.le_refl _) (by omega)) (by simp)) ?_
    refine Outs.trans (Outs.of_outside (o := slot w 3) (n := 8 * (w + 2))
      (out₄.mono (Nat.le_refl _) (by omega)) (by simp)) ?_
    exact Outs.of_outside (o := slot w o) (n := 8 * (w + 2)) (out₅.mono (Nat.le_refl _) (by omega)) (by simp)
  · exact (((k₂.trans k₃).trans k₄).trans k₅).mono

end VG.Proof.Bignum.PPC64LE
