module

-- separate module: the algebra it imports stays out of the modules that only
-- use the contract (`Ghash.lean`), and it builds beside PCLMULQDQ's proof.
public import VerifiedGarbage.Impl.Gcm.X86
public import VerifiedGarbage.Proof.Gcm.X86.Ghash
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseLanes
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.SseWord
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Gcm.Poly
import VerifiedGarbage.Proof.Gcm.X86.Rev
meta import VerifiedGarbage.Impl.Gcm.X86
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Gcm.X86.Ghash

/-!
# GHASH on x86 (32-bit), in SSE2

The proof of the baseline implementation (`Impl/Gcm/X86.lean`), in the ring
`Q` of `Proof/Gcm/Poly.lean`.
-/

/-! ## The arithmetic

What the pieces of `Impl.Gcm.X86` compute, on whole registers and in `Q`. -/

section

namespace VG.Proof.Gcm.X86.Sse2

open VG VG.X86 VG.X86.RegUpd VG.X86.Lanes VG.Proof.Gcm VG.Proof.Gcm.Poly Polynomial
open VG.Proof.Gcm.X86 (revMask GPre hP yP dP sP nBlk hR yR dR sR aR rR)
open VG.Impl.Gcm.X86 (slot acc bcast)
open VG.Spec.Gcm (Block blockAt)

/-! ## The byte reversal -/

/-- `swap`'s constant, in each doubleword. -/
def lowB : BitVec 128 := shufDwords ((0 : BitVec 96) ++ Impl.Gcm.X86.lowBytes) 0

theorem dword_lowB {i : Nat} (hi : i < 4) : dword lowB i = 0x00ff00ff#32 := by
  rw [lowB, bcast_L, dword_L _ hi]; rfl

/-- What `swap` computes. -/
def swapV (v : BitVec 128) : BitVec 128 :=
  let a := shufHighWords (shufLowWords (shufDwords v 0x1b) 0xb1) 0xb1
  XBinOp.eval .por (XShiftOp.eval .pslld (XBinOp.eval .pand a lowB) 8)
    (XBinOp.eval .pand (XShiftOp.eval .psrld a 8) lowB)

theorem dword_rev (v : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .pshufb v revMask) i = bswap (dword v (3 - i)) := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  obtain ⟨j, r, hj, hr, rfl⟩ : ∃ j r, j < 4 ∧ r < 8 ∧ m = 8 * j + r :=
    ⟨m / 8, m % 8, by omega_arith, by omega_arith, by omega_arith⟩
  rw [getLsbD_dword, decide_eq_true hm, Bool.true_and, pshufb_rev,
    show 32 * i + (8 * j + r) = 8 * (4 * i + j) + r by omega_arith, getLsbD_ofBytes _ (by omega_arith) hr,
    getLsbD_bswap_block _ hj hr]
  simp only [byte, BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and, getLsbD_dword]
  rcases cases4 hj with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [↓reduceIte, Nat.reduceEqDiff, decide_eq_true, Bool.true_and] <;>
    exact congrArg _ (by omega)

theorem bswap_masks (d : BitVec 32) :
    ((d.rotateLeft 16 &&& 0x00ff00ff#32) <<< 8 ||| (d.rotateLeft 16 >>> 8 &&& 0x00ff00ff#32)) = bswap d := by
  have hk : ∀ m < 32, (0x00ff00ff#32).getLsbD m = decide (m % 16 < 8) := by decide +kernel
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  obtain ⟨j, r, hj, hr, rfl⟩ : ∃ j r, j < 4 ∧ r < 8 ∧ m = 8 * j + r :=
    ⟨m / 8, m % 8, by omega_arith, by omega_arith, by omega_arith⟩
  rw [getLsbD_bswap_block _ hj hr]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_rotateLeft, hk _ hm]
  rcases cases4 hj with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [↓reduceIte, Nat.reduceEqDiff, decide_eq_true, decide_eq_false, Bool.true_and,
      Bool.false_and, Bool.and_false, Bool.and_true, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false,
      hk, ite_eq_left, ite_eq_right, Nat.reduceMod] <;>
    exact congrArg _ (by omega)

theorem swapV_eq (v : BitVec 128) : swapV v = XBinOp.eval .pshufb v revMask := by
  have h : ∀ i < 4, dword (swapV v) i = dword (XBinOp.eval .pshufb v revMask) i := fun i hi => by
    rw [dword_rev v hi, swapV, dword_por, dword_pslld _ 8 (by decide) hi, dword_pand, dword_pand,
      dword_psrld _ 8 (by decide) hi, dword_lowB hi, dword_rot16 _ hi, dword_shufDwords _ _ hi,
      ← bswap_masks]
    rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl
  exact ext_dword (h 0 (by decide)) (h 1 (by decide)) (h 2 (by decide)) (h 3 (by decide))

/-! ## Multiplication by `x` -/

/-- `rMask`'s value. -/
def rM : BitVec 128 := ofDwords 0 0x80000000#32 0 0xe1000000#32

/-- What `mulX` computes. -/
def mulXV (v : BitVec 128) : BitVec 128 :=
  XBinOp.eval .pxor (XShiftOp.eval .psrlq v 1)
    (XBinOp.eval .pand (shufDwords (XShiftOp.eval .psraw (XShiftOp.eval .psllq v 63) 15) 0x4e) rM)

theorem shl63 (q : BitVec 64) : q <<< 63 = if q.getLsbD 0 then 0x8000000000000000#64 else 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_shiftLeft]
  by_cases h : i = 63
  · subst h; cases q.getLsbD 0 <;> simp
  · have h' : ¬ 63 ≤ i := by omega_arith
    have : ∀ i < 63, (0x8000000000000000#64).getLsbD i = false := by decide +kernel
    cases q.getLsbD 0 <;> simp [this i (by omega_arith), show i < 63 by omega_arith]

/-- The bits that `mulX` adds to the shifted halves. -/
theorem mulX_carry (c d : Bool) :
    XBinOp.eval .pand (shufDwords (XShiftOp.eval .psraw
      ((if c then 0x8000000000000000#64 else 0) ++ (if d then 0x8000000000000000#64 else 0 : BitVec 64)) 15) 0x4e)
      rM = (if d then 0xe100000000000000#64 else 0) ++ (if c then 0x8000000000000000#64 else 0) := by
  cases c <;> cases d <;> decide +kernel

theorem mulXV_eq (v : BitVec 128) :
    mulXV v = if v.getLsbD 0 then (v >>> 1) ^^^ Spec.Gcm.R else v >>> 1 := by
  have e : XShiftOp.eval .psllq v 63 = (qword v 1 <<< 63) ++ (qword v 0 <<< 63) := rfl
  have e' : XShiftOp.eval .psrlq v 1 = (qword v 1 >>> 1) ++ (qword v 0 >>> 1) := rfl
  have hR : ∀ i < 128, Spec.Gcm.R.getLsbD i = if i < 64 then false else (0xe100000000000000#64).getLsbD (i - 64) := by
    decide +kernel
  have h8 : ∀ i < 64, (0x8000000000000000#64).getLsbD i = decide (i = 63) := by decide +kernel
  have q0 : (qword v 0).getLsbD 0 = v.getLsbD 0 := by simp [qword]
  have q1 : (qword v 1).getLsbD 0 = v.getLsbD 64 := by simp [qword]
  rw [mulXV, e, e', shl63, shl63, mulX_carry, q0, q1]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight]
  by_cases h : i < 64
  · have e2 : (if v.getLsbD 0 = true then v >>> 1 ^^^ Spec.Gcm.R else v >>> 1).getLsbD i = v.getLsbD (1 + i) := by
      split <;> simp [hR i hi, h]
    rw [e2]
    simp only [h, ite_true, qword, BitVec.getLsbD_extractLsb', Nat.mul_zero, Nat.zero_add]
    by_cases h63 : i = 63
    · subst h63; cases v.getLsbD 64 <;> simp
    · cases v.getLsbD 64 <;> simp [h8 i h, h63, show 1 + i < 64 by omega_arith]
  · simp only [h, ite_false, qword, BitVec.getLsbD_extractLsb']
    have e3 : (decide (1 + (i - 64) < 64) && v.getLsbD (64 * 1 + (1 + (i - 64)))) = v.getLsbD (1 + i) := by
      by_cases h' : i = 127
      · subst h'; simp
      · rw [decide_eq_true (by omega_arith), Bool.true_and]; exact congrArg _ (by omega_arith)
    rw [e3]
    cases v.getLsbD 0
    · simp
    · simp [hR i hi, h]

theorem φ_mulXV (v : BitVec 128) : φ (mulXV v) = x * φ v := by rw [mulXV_eq, φ_shr1]

/-! ## The masks -/

/-- The words of `d`, each shifted left by `k` bits. -/
def shlW (d : BitVec 128) (k : Nat) : BitVec 128 := ofWords fun i => word d i <<< k

theorem shlW_zero (d : BitVec 128) : shlW d 0 = d :=
  ext_word fun i hi => by rw [shlW, word_ofWords _ hi, BitVec.shiftLeft_zero]

theorem shlW_succ (d : BitVec 128) (k : Nat) : XBinOp.eval .paddw (shlW d k) (shlW d k) = shlW d (k + 1) :=
  ext_word fun i hi => by
    rw [word_paddw _ _ hi, shlW, word_ofWords _ hi, shlW, word_ofWords _ hi, BitVec.shiftLeft_add]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft (n := 1), Nat.shiftLeft_eq]
    congr 1; omega_arith

/-- The bit of doubleword `l` of `d` that a step takes after `k` shifts. -/
def bitOf (d : BitVec 128) (l k : Nat) : Bool := (word d (2 * l)).getLsbD (15 - k)

/-- The words of each doubleword are equal. -/
def Dup (d : BitVec 128) : Prop := ∀ l < 4, word d (2 * l + 1) = word d (2 * l)

theorem psraw15 (w : BitVec 16) : w.sshiftRight 15 = if w.msb then BitVec.allOnes 16 else 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_sshiftRight]
  by_cases h : i = 0
  · subst h; cases hm : w.msb <;> simp_all [BitVec.msb_eq_getLsbD_last]
  · simp only [show ¬ 15 + i < 16 by omega_arith, ite_false, show ¬ 16 ≤ i by omega_arith, decide_false, Bool.not_false, Bool.true_and]
    cases w.msb
    · simp
    · simp only [ite_true, BitVec.getLsbD_allOnes, hi, decide_true]

theorem word_mask (d : BitVec 128) {i k : Nat} (hi : i < 8) (hk : k < 16) :
    word (XShiftOp.eval .psraw (shlW d k) 15) i =
      if (word d i).getLsbD (15 - k) then BitVec.allOnes 16 else 0 := by
  rw [word_psraw _ _ hi, show min (15 : BitVec 8).toNat 16 = 15 from rfl, psraw15, shlW, word_ofWords _ hi,
    BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]
  simp only [show 16 - 1 < 16 by decide, decide_true, Bool.true_and, show ¬ 16 - 1 < k by omega_arith, decide_false,
    Bool.not_false]

/-- A mask, broadcast. -/
theorem mask_bcast (d : BitVec 128) (hd : Dup d) {l k : Nat} (hl : l < 4) (hk : k < 16) :
    shufDwords (XShiftOp.eval .psraw (shlW d k) 15) (BitVec.ofNat 8 (0x55 * l)) =
      if bitOf d l k then BitVec.allOnes 128 else 0 := by
  have e : dword (XShiftOp.eval .psraw (shlW d k) 15) l = if bitOf d l k then BitVec.allOnes 32 else 0 := by
    apply BitVec.eq_of_getLsbD_eq; intro m hm
    have w : ∀ t < 2, word (XShiftOp.eval .psraw (shlW d k) 15) (2 * l + t) =
        if bitOf d l k then BitVec.allOnes 16 else 0 := fun t ht => by
      rw [word_mask d (by omega_arith) hk, bitOf]
      rcases (by omega_arith : t = 0 ∨ t = 1) with rfl | rfl
      · rfl
      · rw [hd l hl]
    have := congrArg (BitVec.getLsbD · (m % 16)) (w (m / 16) (by omega_arith))
    simp only [getLsbD_word _ _ _ (Nat.mod_lt m (show 16 > 0 by decide)),
      show 16 * (2 * l + m / 16) + m % 16 = 32 * l + m by omega_arith] at this
    rw [getLsbD_dword, decide_eq_true hm, Bool.true_and, this]
    cases bitOf d l k
    · simp
    · simp only [ite_true, BitVec.getLsbD_allOnes, hm, show m % 16 < 16 by omega_arith, decide_true]
  have h : ∀ i < 4, dword (shufDwords (XShiftOp.eval .psraw (shlW d k) 15) (BitVec.ofNat 8 (0x55 * l))) i =
      dword (if bitOf d l k then BitVec.allOnes 128 else 0) i := fun i hi => by
    rw [dword_shufDwords_bcast _ hl hi, e]
    cases bitOf d l k
    · apply BitVec.eq_of_getLsbD_eq; intro m hm; simp [dword]
    · apply BitVec.eq_of_getLsbD_eq; intro m hm
      simp only [ite_true, getLsbD_dword, BitVec.getLsbD_allOnes, hm, show 32 * i + m < 128 by omega_arith, decide_true, Bool.true_and]
  exact ext_dword (h 0 (by decide)) (h 1 (by decide)) (h 2 (by decide)) (h 3 (by decide))

/-- A table entry under a mask. -/
def pick (b : Bool) (t : BitVec 128) : BitVec 128 := if b then t else 0

theorem mask_pand (d : BitVec 128) (hd : Dup d) {l k : Nat} (hl : l < 4) (hk : k < 16) (t : BitVec 128) :
    XBinOp.eval .pand (shufDwords (XShiftOp.eval .psraw (shlW d k) 15) (BitVec.ofNat 8 (0x55 * l))) t =
      pick (bitOf d l k) t := by
  rw [mask_bcast d hd hl hk, pick]
  show (if bitOf d l k then _ else _) &&& t = _
  cases bitOf d l k
  · exact BitVec.zero_and
  · exact BitVec.allOnes_and

theorem φ_pick (b : Bool) (t : BitVec 128) : φ (pick b t) = if b then φ t else 0 := by
  cases b
  · exact φ_zero
  · rfl

/-! ## Sums without reduction -/

theorem gp_shift (v : BitVec 128) {r : Nat} (hr : r ≤ 128) :
    gp (v >>> r) + X ^ 128 * gp (v <<< (128 - r)) = X ^ r * gp v := by
  ext d
  simp only [coeff_add, coeff_X_pow_mul', coeff_gp]
  simp only [BitVec.getMsbD_ushiftRight, BitVec.getMsbD_shiftLeft]
  by_cases h1 : d < r
  · simp only [show ¬ r ≤ d by omega_arith, show ¬ 128 ≤ d by omega_arith, ite_false, h1, decide_true, Bool.not_true, Bool.false_and, Bool.and_false, add_zero]
    rfl
  · by_cases h2 : d < 128
    · simp only [show r ≤ d by omega_arith, show ¬ 128 ≤ d by omega_arith, ite_false, ite_true, h1, h2, decide_true, decide_false, Bool.not_false, Bool.true_and, add_zero]
    · simp only [show r ≤ d by omega_arith, show 128 ≤ d by omega_arith, ite_true, h2, decide_false, Bool.false_and]
      rw [show d - 128 + (128 - r) = d - r by omega_arith]
      simp [bit]

/-- `Z + x¹²⁸·O`. -/
noncomputable def wide (z o : BitVec 128) : Q := φ z + x ^ 128 * φ o

/-- The lowest `n` bits of `o` are 0. -/
def Low (o : BitVec 128) (n : Nat) : Prop := ∀ i < n, o.getLsbD i = false

theorem φ_shift (v : BitVec 128) {r : Nat} (hr : r ≤ 128) :
    wide (v >>> r) (v <<< (128 - r)) = x ^ r * φ v := by
  have h := congrArg (AdjoinRoot.mk g) (gp_shift v hr)
  simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X] at h
  exact h

theorem shl_low {o : BitVec 128} {r : Nat} (hr : r ≤ 128) (h : Low o r) : o <<< (128 - r) = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_shiftLeft, show (0 : BitVec 128).getLsbD i = false from BitVec.getLsbD_zero]
  by_cases h' : i < 128 - r
  · simp [h']
  · simp [h (i - (128 - r)) (by omega_arith)]

theorem φ_shr {o : BitVec 128} {r : Nat} (hr : r ≤ 128) (h : Low o r) : φ (o >>> r) = x ^ r * φ o := by
  rw [← φ_shift o hr, wide, shl_low hr h, φ_zero, mul_zero, add_zero]

/-- `(z, o)·xʳ`, where `o` has room. -/
theorem wide_shift {z o : BitVec 128} {r : Nat} (hr : r ≤ 128) (h : Low o r) :
    wide (z >>> r) (o >>> r ^^^ z <<< (128 - r)) = x ^ r * wide z o := by
  have h' := φ_shift z hr
  rw [wide] at h' ⊢
  rw [φ_xor, φ_shr hr h, wide]
  linear_combination h'

theorem wide_xor (z o z' o' : BitVec 128) : wide (z ^^^ z') (o ^^^ o') = wide z o + wide z' o' := by
  simp only [wide, φ_xor]; ring

theorem wide_xor_left (z o z' : BitVec 128) : wide (z ^^^ z') o = wide z o + φ z' := by
  simp only [wide, φ_xor]; ring

theorem low_shl (z : BitVec 128) (r : Nat) : Low (z <<< r) r := fun i hi => by
  simp [BitVec.getLsbD_shiftLeft, hi]

theorem low_shr {o : BitVec 128} {n r : Nat} (h : Low o (n + r)) : Low (o >>> r) n := fun i hi => by
  rw [BitVec.getLsbD_ushiftRight]; exact h _ (by omega_arith)

theorem low_xor {o o' : BitVec 128} {n : Nat} (h : Low o n) (h' : Low o' n) : Low (o ^^^ o') n := fun i hi => by
  rw [BitVec.getLsbD_xor, h i hi, h' i hi]; rfl

theorem Low.mono {o : BitVec 128} {n m : Nat} (h : Low o n) (hm : m ≤ n) : Low o m :=
  fun i hi => h i (by omega_arith)

/-! ## The reduction -/

theorem φ_reduce {z o : BitVec 128} (h : Low o 8) :
    φ (z ^^^ o ^^^ o >>> 1 ^^^ o >>> 2 ^^^ o >>> 7) = wide z o := by
  simp only [φ_xor, wide, φ_shr (r := 1) (by decide) (h.mono (by decide)),
    φ_shr (r := 2) (by decide) (h.mono (by decide)), φ_shr (r := 7) (by decide) (h.mono (by decide)), x128]
  ring

/-- `reduce`'s shifts of `o`, of each half, and the bits carried between them. -/
theorem shr_halves (o : BitVec 128) {r : Nat} (h0 : 0 < r) (hr : r < 64) :
    o >>> r = ((qword o 1 >>> r) ++ (qword o 0 >>> r)) ^^^ ((qword o 1 <<< (64 - r)) ++ (qword o 0 <<< (64 - r))) >>> 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, qword,
    BitVec.getLsbD_extractLsb']
  by_cases h1 : i < 64
  · simp only [h1, ite_true, show ¬ 64 + i < 64 by omega_arith, ite_false, show 64 + i - 64 = i by omega_arith,
      decide_true, Bool.true_and, Nat.mul_zero, Nat.zero_add, Nat.mul_one]
    by_cases h2 : r + i < 64
    · simp only [h2, show i < 64 - r by omega_arith, decide_true, Bool.true_and, Bool.not_true, Bool.false_and, Bool.xor_false]
    · simp only [h2, show ¬ i < 64 - r by omega_arith, show i - (64 - r) < 64 by omega_arith, decide_true, decide_false,
        Bool.true_and, Bool.not_false, Bool.false_and, Bool.false_xor]
      exact congrArg _ (by omega_arith)
  · simp only [h1, ite_false, show ¬ 64 + i < 64 by omega_arith, show ¬ 64 + i - 64 < 64 by omega_arith, decide_false,
      Bool.false_and, Bool.xor_false, Nat.mul_one]
    by_cases h2 : r + (i - 64) < 64
    · simp only [h2, decide_true, Bool.true_and]; exact congrArg _ (by omega_arith)
    · simp only [h2, decide_false, Bool.false_and]; exact BitVec.getLsbD_of_ge _ _ (by omega_arith)

/-- What `reduce` computes. -/
def reduceV (z o : BitVec 128) : BitVec 128 :=
  let a := XShiftOp.eval .psllq o 57
  let b := XShiftOp.eval .psllq a 5
  let c := XShiftOp.eval .psllq b 1
  let z' := z ^^^ XShiftOp.eval .psrldq ((a ^^^ b) ^^^ c) 8
  let o1 := XShiftOp.eval .psrlq o 1
  let o2 := XShiftOp.eval .psrlq o1 1
  let o7 := XShiftOp.eval .psrlq o2 5
  (((z' ^^^ o) ^^^ o1) ^^^ o2) ^^^ o7

theorem qword_hi (h l : BitVec 64) : qword (h ++ l) 1 = h := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    Nat.mul_one, show ¬ 64 + i < 64 by omega_arith, ite_false, Nat.add_sub_cancel_left]

theorem qword_lo (h l : BitVec 64) : qword (h ++ l) 0 = l := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    Nat.mul_zero, Nat.zero_add, ite_true]

theorem psllq_eq (o : BitVec 128) {n : BitVec 8} (hn : n.toNat < 64) :
    XShiftOp.eval .psllq o n = (qword o 1 <<< n.toNat) ++ (qword o 0 <<< n.toNat) := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega_arith, ite_false]

theorem psrlq_eq (o : BitVec 128) {n : BitVec 8} (hn : n.toNat < 64) :
    XShiftOp.eval .psrlq o n = (qword o 1 >>> n.toNat) ++ (qword o 0 >>> n.toNat) := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega_arith, ite_false]

theorem psllq_psllq (o : BitVec 128) {m n k : BitVec 8} (hm : m.toNat < 64) (hn : n.toNat < 64)
    (hk : m.toNat + n.toNat = k.toNat) (hk' : k.toNat < 64) :
    XShiftOp.eval .psllq (XShiftOp.eval .psllq o m) n = XShiftOp.eval .psllq o k := by
  rw [psllq_eq _ hn, psllq_eq _ hm, qword_hi, qword_lo, psllq_eq _ hk', ← hk, BitVec.shiftLeft_add, BitVec.shiftLeft_add]

theorem psrlq_psrlq (o : BitVec 128) {m n k : BitVec 8} (hm : m.toNat < 64) (hn : n.toNat < 64)
    (hk : m.toNat + n.toNat = k.toNat) (hk' : k.toNat < 64) :
    XShiftOp.eval .psrlq (XShiftOp.eval .psrlq o m) n = XShiftOp.eval .psrlq o k := by
  rw [psrlq_eq _ hn, psrlq_eq _ hm, qword_hi, qword_lo, psrlq_eq _ hk', ← hk, BitVec.shiftRight_add, BitVec.shiftRight_add]

theorem shr_eval (o : BitVec 128) {r k : BitVec 8} (h0 : 0 < r.toNat) (hr : r.toNat < 64) (hk : k.toNat = 64 - r.toNat) :
    o >>> r.toNat = XShiftOp.eval .psrlq o r ^^^ XShiftOp.eval .psllq o k >>> 64 := by
  rw [shr_halves o h0 hr, psrlq_eq _ hr, psllq_eq _ (by omega_arith), hk]

theorem xors (z o o1 o2 o7 a b c : BitVec 128) :
    (((z ^^^ ((a ^^^ b) ^^^ c)) ^^^ o) ^^^ o1) ^^^ o2 ^^^ o7 = z ^^^ o ^^^ (o1 ^^^ c) ^^^ (o2 ^^^ b) ^^^ (o7 ^^^ a) := by
  ac_rfl

theorem reduceV_eq (z o : BitVec 128) : reduceV z o = z ^^^ o ^^^ o >>> 1 ^^^ o >>> 2 ^^^ o >>> 7 := by
  have s8 : ∀ v : BitVec 128, XShiftOp.eval .psrldq v 8 = v >>> 64 := fun _ => rfl
  have e1 : o >>> 1 = _ := shr_eval o (r := 1) (k := 63) (by decide) (by decide) (by decide)
  have e2 : o >>> 2 = _ := shr_eval o (r := 2) (k := 62) (by decide) (by decide) (by decide)
  have e7 : o >>> 7 = _ := shr_eval o (r := 7) (k := 57) (by decide) (by decide) (by decide)
  rw [reduceV, s8, BitVec.ushiftRight_xor_distrib, BitVec.ushiftRight_xor_distrib,
    psllq_psllq o (m := 57) (n := 5) (k := 62) (by decide) (by decide) (by decide) (by decide),
    psllq_psllq o (m := 62) (n := 1) (k := 63) (by decide) (by decide) (by decide) (by decide),
    psrlq_psrlq o (m := 1) (n := 1) (k := 2) (by decide) (by decide) (by decide) (by decide),
    psrlq_psrlq o (m := 2) (n := 5) (k := 7) (by decide) (by decide) (by decide) (by decide), e1, e2, e7]
  exact xors _ _ _ _ _ _ _ _

theorem φ_reduceV {z o : BitVec 128} (h : Low o 8) : φ (reduceV z o) = wide z o := by
  rw [reduceV_eq, φ_reduce h]


/-! ## What a piece changes -/

abbrev sA (s₀ : State) (k : Nat) : Addr := addr (sP s₀) (16 * k)

/-- A piece changes vector registers and the slots `ks` only. -/
structure Stp (s₀ : State) (ks : List Nat) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [sR s₀] s.mem s'.mem
  slots : ∀ j < 16, j ∉ ks → s'.mem.readW (sA s₀ j) 128 = s.mem.readW (sA s₀ j) 128

theorem Stp.of_eq {s₀ s s' : State} (g : s'.gpr = s.gpr) (r : s'.rd = s.rd) (w : s'.wr = s.wr) (m : s'.mem = s.mem) :
    Stp s₀ [] s s' := ⟨g, r, w, by rw [m]; exact Frame.refl _ _, fun j _ _ => by rw [m]⟩

/-- A goal `Stp s₀ [] s s'`, with `s'` writes of vector registers of `s`. -/
local macro "stp_vec" : term => `(Stp.of_eq (by simp only [gpr_setXmm]) (by simp only [rd_setXmm])
  (by simp only [wr_setXmm]) (by simp only [mem_setXmm]))

theorem Stp.trans {s₀ : State} {ks ks' : List Nat} {s s' s'' : State} (h : Stp s₀ ks s s') (h' : Stp s₀ ks' s' s'') :
    Stp s₀ (ks ++ ks') s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.rd.trans h.rd, h'.wr.trans h.wr, h.frame.trans h'.frame, fun j hj hn => by
    rw [List.mem_append, not_or] at hn
    rw [h'.slots j hj hn.2, h.slots j hj hn.1]⟩

theorem slot_ea {s₀ s : State} (hc : s.gpr .edx = sP s₀) (k : Nat) : s.ea (slot k) = sA s₀ k := by
  simp only [slot, Impl.Gcm.X86.at_, State.ea, hc, sA, addr]

theorem slot_in {s₀ : State} (hp : GPre s₀) {k : Nat} (hk : k < 16) : (sR s₀).Contains (sA s₀ k) 16 :=
  Proof.Aes.X86.reg_contains hp.fS (by omega_arith) (by decide)

theorem slot_wr {s₀ s : State} (hp : GPre s₀) (hw : s.wr = s₀.wr) {k : Nat} (hk : k < 16) :
    InRegions s.wr (sA s₀ k) 16 := by
  rw [hw, hp.wr]
  exact ⟨sR s₀, by simp only [List.mem_cons, List.not_mem_nil, or_false, or_true], slot_in hp hk⟩

theorem slot_rd {s₀ s : State} (hp : GPre s₀) (hw : s.wr = s₀.wr) {k : Nat} (hk : k < 16) :
    InRegions (s.rd ++ s.wr) (sA s₀ k) 16 := Proof.Aes.X86.in_rd (slot_wr hp hw hk)

theorem slot_sep {s₀ : State} (hp : GPre s₀) {j k : Nat} (hj : j < 16) (hk : k < 16) (hne : j ≠ k) :
    Mem.Sep (sA s₀ j) (128 / 8) (sA s₀ k) (128 / 8) :=
  (Proof.Aes.X86.part_disj hp.fS (by omega_arith) (by omega_arith)
    (by omega_arith)).sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- A slot's load. -/
theorem ld_exec {s₀ s : State} (hp : GPre s₀) (hc : s.gpr .edx = sP s₀) (hw : s.wr = s₀.wr) {k : Nat} (hk : k < 16)
    (r : XReg) : exec (.movdquLoad r (slot k)) s = some (s.setXmm r (s.mem.readW (sA s₀ k) 128)) := by
  simp only [exec, State.load128, slot_ea hc, slot_rd hp hw hk, ite_true, Option.map_some]

/-- The state after a slot's store. -/
abbrev put (s₀ s : State) (k : Nat) (v : BitVec 128) : State := { s with mem := s.mem.writeW (sA s₀ k) v }

theorem st_exec {s₀ s : State} (hp : GPre s₀) (hc : s.gpr .edx = sP s₀) (hw : s.wr = s₀.wr) {k : Nat} (hk : k < 16)
    (r : XReg) : exec (.movdquStore (slot k) r) s = some (put s₀ s k (s.xmm r)) := by
  simp only [exec, State.store128, slot_ea hc, slot_wr hp hw hk, ite_true]

theorem put_stp {s₀ : State} (hp : GPre s₀) (s : State) {k : Nat} (hk : k < 16) (v : BitVec 128) :
    Stp s₀ [k] s (put s₀ s k v) :=
  ⟨rfl, rfl, rfl, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (slot_in hp hk), fun j hj hn =>
    Mem.readW_writeW_sep (slot_sep hp hj hk fun h => hn (by rw [h]; exact List.mem_singleton_self _)) (by decide)⟩

theorem put_read {s₀ s : State} (k : Nat) (v : BitVec 128) : (put s₀ s k v).mem.readW (sA s₀ k) 128 = v :=
  Mem.readW_writeW_self _ _ 16 _ (by decide)

/-! ## A group of eight steps -/

abbrev H (s₀ : State) : Block := blockAt s₀.mem ((hP s₀).setWidth 64)

/-- The table. -/
def Tab (s₀ : State) (m : Mem) : Prop := ∀ j < 8, φ (m.readW (sA s₀ j) 128) = x ^ j * φ (H s₀)

theorem Stp.tab {s₀ : State} {ks : List Nat} {s s' : State} (h : Stp s₀ ks s s') (hk : ∀ j < 8, j ∉ ks)
    (ht : Tab s₀ s.mem) : Tab s₀ s'.mem := fun j hj => by
  rw [h.slots j (by omega_arith) (hk j hj)]; exact ht j hj

theorem mask_pand3 (d : BitVec 128) (hd : Dup d) {k : Nat} (hk : k < 16) (t : BitVec 128) :
    XBinOp.eval .pand (shufDwords (XShiftOp.eval .psraw (shlW d k) 15) 0xff) t = pick (bitOf d 3 k) t :=
  mask_pand d hd (l := 3) (by decide) hk t

theorem mask_pand2 (d : BitVec 128) (hd : Dup d) {k : Nat} (hk : k < 16) (t : BitVec 128) :
    XBinOp.eval .pand (shufDwords (XShiftOp.eval .psraw (shlW d k) 15) 0xaa) t = pick (bitOf d 2 k) t :=
  mask_pand d hd (l := 2) (by decide) hk t

theorem mask_pand1 (d : BitVec 128) (hd : Dup d) {k : Nat} (hk : k < 16) (t : BitVec 128) :
    XBinOp.eval .pand (shufDwords (XShiftOp.eval .psraw (shlW d k) 15) 0x55) t = pick (bitOf d 1 k) t :=
  mask_pand d hd (l := 1) (by decide) hk t

theorem mask_pand0 (d : BitVec 128) (hd : Dup d) {k : Nat} (hk : k < 16) (t : BitVec 128) :
    XBinOp.eval .pand (shufDwords (XShiftOp.eval .psraw (shlW d k) 15) 0x00) t = pick (bitOf d 0 k) t :=
  mask_pand d hd (l := 0) (by decide) hk t

/-- A state with the group's masks and table. -/
structure Mid (s₀ s : State) (d : BitVec 128) (k : Nat) : Prop where
  edx : s.gpr .edx = sP s₀
  wr : s.wr = s₀.wr
  tab : Tab s₀ s.mem
  words : s.xmm .xmm4 = shlW d k

theorem Mid.next {s₀ s s' : State} {d : BitVec 128} {k k' : Nat} (h : Mid s₀ s d k) (o : Stp s₀ [] s s')
    (hw : s'.xmm .xmm4 = shlW d k') : Mid s₀ s' d k' :=
  ⟨by rw [o.gpr]; exact h.edx, o.wr.trans h.wr, o.tab (fun _ _ => List.not_mem_nil) h.tab, hw⟩

theorem masks_ok {s₀ s : State} (hp : GPre s₀) {d : BitVec 128} {k i : Nat} (hi : i < 8) (h : Mid s₀ s d k) :
    WP isa (.block (Impl.Gcm.X86.masks i)) s fun s' =>
      s'.xmm .xmm6 = s.mem.readW (sA s₀ i) 128 ∧ s'.xmm .xmm5 = XShiftOp.eval .psraw (shlW d k) 15 ∧
      s'.xmm .xmm4 = shlW d (k + 1) ∧ (∀ q < 4, s'.xmm (acc q) = s.xmm (acc q)) ∧ Stp s₀ [] s s' := by
  apply WP.of_runBlock
  rw [Impl.Gcm.X86.masks, runBlock_cons, ld_exec hp h.edx h.wr (show i < 16 by omega_arith), runStep_some]
  simp only [runBlock_cons, runStep_some, exec, XOp.exec, isa, runBlock_nil, xmm_setXmm, eval_movdqa, reduceCtorEq, ↓reduceIte, Option.some.injEq,
    exists_eq_left', h.words, shlW_succ, true_and]
  refine ⟨fun q hq => ?_, stp_vec⟩
  rcases cases4 hq with rfl | rfl | rfl | rfl <;> simp only [acc, reduceCtorEq, ↓reduceIte]

theorem sets_ok {s₀ s : State} {d : BitVec 128} (hd : Dup d) {k : Nat} (hk : k < 16)
    (h5 : s.xmm .xmm5 = XShiftOp.eval .psraw (shlW d k) 15) :
    WP isa (.block (Impl.Gcm.X86.set 0 ++ (Impl.Gcm.X86.set 1 ++ (Impl.Gcm.X86.set 2 ++ Impl.Gcm.X86.set 3)))) s fun s' =>
      (∀ q < 4, s'.xmm (acc q) = pick (bitOf d (3 - q) k) (s.xmm .xmm6)) ∧ s'.xmm .xmm4 = s.xmm .xmm4 ∧ Stp s₀ [] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.set, acc, bcast, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    exec, XOp.exec, isa, runBlock_nil, xmm_setXmm, reduceCtorEq, ↓reduceIte, Option.some.injEq,
    exists_eq_left', h5, mask_pand0 d hd hk, mask_pand1 d hd hk, mask_pand2 d hd hk, mask_pand3 d hd hk]
  refine ⟨fun q hq => ?_, trivial, stp_vec⟩
  rcases cases4 hq with rfl | rfl | rfl | rfl <;> simp only [reduceCtorEq, ↓reduceIte, Nat.reduceSub]

theorem adds_ok {s₀ s : State} {d : BitVec 128} (hd : Dup d) {k : Nat} (hk : k < 16)
    (h5 : s.xmm .xmm5 = XShiftOp.eval .psraw (shlW d k) 15) :
    WP isa (.block (Impl.Gcm.X86.add 0 ++ (Impl.Gcm.X86.add 1 ++ (Impl.Gcm.X86.add 2 ++ Impl.Gcm.X86.add 3)))) s fun s' =>
      (∀ q < 4, s'.xmm (acc q) = s.xmm (acc q) ^^^ pick (bitOf d (3 - q) k) (s.xmm .xmm6)) ∧
      s'.xmm .xmm4 = s.xmm .xmm4 ∧ Stp s₀ [] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.add, acc, bcast, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    exec, XOp.exec, isa, runBlock_nil, xmm_setXmm, reduceCtorEq, ↓reduceIte, Option.some.injEq,
    exists_eq_left', h5, mask_pand0 d hd hk, mask_pand1 d hd hk, mask_pand2 d hd hk, mask_pand3 d hd hk]
  refine ⟨fun q hq => ?_, trivial, stp_vec⟩
  rcases cases4 hq with rfl | rfl | rfl | rfl <;> simp only [reduceCtorEq, ↓reduceIte, Nat.reduceSub] <;> rfl

/-- The bits `k` to `k + n` of the words of doubleword `l`, as a polynomial. -/
noncomputable def bits (d : BitVec 128) (l k n : Nat) : Q :=
  ∑ i ∈ Finset.range n, if bitOf d l (k + i) then x ^ i else 0

theorem bits_succ (d : BitVec 128) (l k n : Nat) :
    bits d l k (n + 1) = bits d l k n + if bitOf d l (k + n) then x ^ n else 0 := Finset.sum_range_succ _ _

/-- After `n` steps of a group that started in `t`. -/
structure GInv (s₀ t : State) (d : BitVec 128) (k n : Nat) (s : State) : Prop where
  mid : Mid s₀ s d (k + n)
  acc : ∀ q < 4, φ (s.xmm (acc q)) = bits d (3 - q) k n * φ (H s₀)
  stp : Stp s₀ [] t s

theorem ite_mul_pow (b : Bool) (i : Nat) (h : Q) :
    (if b then x ^ i * h else 0) = (if b then x ^ i else 0) * h := by
  cases b
  · exact (zero_mul h).symm
  · rfl

theorem step0_ok {s₀ s : State} (hp : GPre s₀) {d : BitVec 128} (hd : Dup d) {k : Nat} (hk : k < 16)
    (h : Mid s₀ s d k) : WP isa (.block Impl.Gcm.X86.step0) s (GInv s₀ s d k 1) := by
  rw [Impl.Gcm.X86.step0, WP.block_append_iff]
  refine WP.mono (masks_ok hp (by decide) h) fun s₁ ⟨t₁, m₁, w₁, _, o₁⟩ => ?_
  refine WP.mono (sets_ok (s₀ := s₀) hd hk m₁) fun s₂ ⟨a₂, w₂, o₂⟩ => ?_
  refine ⟨h.next (o₁.trans o₂) (w₂.trans w₁), fun q hq => ?_, o₁.trans o₂⟩
  rw [a₂ q hq, φ_pick, t₁, h.tab 0 (by decide), ite_mul_pow, bits, Finset.sum_range_one, Nat.add_zero]

theorem step_ok {s₀ t s : State} (hp : GPre s₀) {d : BitVec 128} (hd : Dup d) {k n : Nat} (hn : n < 8)
    (hk : k + n < 16) (h : GInv s₀ t d k n s) : WP isa (.block (Impl.Gcm.X86.step n)) s (GInv s₀ t d k (n + 1)) := by
  rw [Impl.Gcm.X86.step, WP.block_append_iff]
  refine WP.mono (masks_ok hp hn h.mid) fun s₁ ⟨t₁, m₁, w₁, a₁, o₁⟩ => ?_
  refine WP.mono (adds_ok (s₀ := s₀) hd hk m₁) fun s₂ ⟨a₂, w₂, o₂⟩ => ?_
  have o := o₁.trans o₂
  refine ⟨h.mid.next o (w₂.trans w₁), fun q hq => ?_, h.stp.trans o⟩
  rw [a₂ q hq, φ_xor, a₁ q hq, h.acc q hq, φ_pick, t₁, h.mid.tab n hn, ite_mul_pow, bits_succ, add_mul]

theorem group_ok {s₀ s : State} (hp : GPre s₀) {d : BitVec 128} (hd : Dup d) {k : Nat} (hk : k ≤ 8)
    (h : Mid s₀ s d k) : WP isa (.block Impl.Gcm.X86.group) s (GInv s₀ s d k 8) := by
  rw [Impl.Gcm.X86.group, WP.block_append_iff]
  refine WP.mono (step0_ok hp hd (by omega_arith) h) fun s₁ h₁ => ?_
  have steps : ∀ n ≤ 7, WP isa (.block ((List.range n).flatMap fun i => Impl.Gcm.X86.step (i + 1))) s₁
      (GInv s₀ s d k (n + 1)) := by
    intro n
    induction n with
    | zero => intro _; exact WP.block_nil h₁
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
      refine WP.mono (ih (by omega_arith)) fun s₂ h₂ => ?_
      rw [List.flatMap_singleton]
      exact step_ok hp hd (by omega_arith) (by omega_arith) h₂
  exact steps 7 (by decide)

/-! ## The sum of a group -/

theorem psrldq_eq (v : BitVec 128) {n : BitVec 8} (hn : n.toNat ≤ 16) : XShiftOp.eval .psrldq v n = v >>> (n.toNat * 8) := by
  simp only [XShiftOp.eval, Nat.min_eq_left hn]

theorem pslldq_eq (v : BitVec 128) {n : BitVec 8} (hn : n.toNat ≤ 16) : XShiftOp.eval .pslldq v n = v <<< (n.toNat * 8) := by
  simp only [XShiftOp.eval, Nat.min_eq_left hn]

theorem psrldq2 (v : BitVec 128) : XShiftOp.eval .psrldq v 2 = v >>> 16 := psrldq_eq v (by decide)
theorem psrldq1 (v : BitVec 128) : XShiftOp.eval .psrldq v 1 = v >>> 8 := psrldq_eq v (by decide)
theorem psrldq8 (v : BitVec 128) : XShiftOp.eval .psrldq v 8 = v >>> 64 := psrldq_eq v (by decide)
theorem pslldq14 (v : BitVec 128) : XShiftOp.eval .pslldq v 14 = v <<< (128 - 16) := pslldq_eq v (by decide)
theorem pslldq15 (v : BitVec 128) : XShiftOp.eval .pslldq v 15 = v <<< (128 - 8) := pslldq_eq v (by decide)
theorem pslldq8 (v : BitVec 128) : XShiftOp.eval .pslldq v 8 = v <<< (128 - 64) := pslldq_eq v (by decide)
theorem pxor_eq (a b : BitVec 128) : XBinOp.eval .pxor a b = a ^^^ b := rfl

theorem shift16_ok {s₀ s : State} {q n : Nat} (hq : q < 3) (hn : n ≤ 112) (hl : Low (s.xmm .xmm5) (n + 16)) :
    WP isa (.block (Impl.Gcm.X86.shift16 q)) s fun s' =>
      wide (s'.xmm .xmm3) (s'.xmm .xmm5) = x ^ 16 * wide (s.xmm .xmm3) (s.xmm .xmm5) + φ (s.xmm (acc q)) ∧
      Low (s'.xmm .xmm5) n ∧ (∀ p < 3, s'.xmm (acc p) = s.xmm (acc p)) ∧ s'.xmm .xmm4 = s.xmm .xmm4 ∧ Stp s₀ [] s s' := by
  have hq' : acc q = .xmm0 ∨ acc q = .xmm1 ∨ acc q = .xmm2 := by
    rcases (by omega_arith : q = 0 ∨ q = 1 ∨ q = 2) with rfl | rfl | rfl <;> decide
  have n3 : acc q ≠ .xmm3 := by rcases hq' with h | h | h <;> rw [h] <;> decide
  have n5 : acc q ≠ .xmm5 := by rcases hq' with h | h | h <;> rw [h] <;> decide
  have n6 : acc q ≠ .xmm6 := by rcases hq' with h | h | h <;> rw [h] <;> decide
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.shift16, runBlock_cons, runStep_some,
    exec, XOp.exec, isa, runBlock_nil, xmm_setXmm, reduceCtorEq, ↓reduceIte, Option.some.injEq,
    exists_eq_left', eval_movdqa, psrldq2, pslldq14, pxor_eq, n3, n5, n6]
  refine ⟨?_, low_xor (low_shr hl) ((low_shl _ _).mono (by omega_arith)), fun p hp => ?_, trivial, stp_vec⟩
  · rw [wide_xor_left, wide_shift (by decide) (hl.mono (by omega_arith))]
  · rcases (by omega_arith : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> simp only [acc, reduceCtorEq, ↓reduceIte]

theorem first_ok {s₀ s : State} :
    WP isa (.block [.xop (.bin .movdqa .xmm5 .xmm3), .xop (.shift .pslldq .xmm5 14), .xop (.shift .psrldq .xmm3 2),
      .xop (.bin .pxor .xmm3 .xmm2)]) s fun s' =>
      wide (s'.xmm .xmm3) (s'.xmm .xmm5) = x ^ 16 * φ (s.xmm (acc 3)) + φ (s.xmm (acc 2)) ∧
      Low (s'.xmm .xmm5) 112 ∧ (∀ p < 3, s'.xmm (acc p) = s.xmm (acc p)) ∧ s'.xmm .xmm4 = s.xmm .xmm4 ∧ Stp s₀ [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some,
    exec, XOp.exec, isa, runBlock_nil, xmm_setXmm, reduceCtorEq, ↓reduceIte, Option.some.injEq,
    exists_eq_left', eval_movdqa, psrldq2, pslldq14, pxor_eq, acc]
  refine ⟨?_, low_shl _ _, fun p hp => ?_, trivial, stp_vec⟩
  · rw [wide_xor_left, φ_shift _ (by decide)]
  · rcases (by omega_arith : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> simp only [reduceCtorEq, ↓reduceIte]

/-- The sum of the accumulators of `s`, each times its power of `x¹⁶`. -/
noncomputable def accs (a : Nat → Q) : Q := a 0 + x ^ 16 * a 1 + x ^ 32 * a 2 + x ^ 48 * a 3

theorem horner_ok {s₀ s : State} :
    WP isa (.block Impl.Gcm.X86.horner) s fun s' =>
      wide (s'.xmm .xmm3) (s'.xmm .xmm5) = accs (fun q => φ (s.xmm (acc q))) ∧ Low (s'.xmm .xmm5) 80 ∧
      s'.xmm .xmm4 = s.xmm .xmm4 ∧ Stp s₀ [] s s' := by
  rw [Impl.Gcm.X86.horner, WP.block_append_iff]
  refine WP.mono (first_ok (s₀ := s₀)) fun s₁ ⟨w₁, l₁, a₁, f₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (shift16_ok (s₀ := s₀) (q := 1) (n := 96) (by decide) (by decide) l₁) fun s₂ ⟨w₂, l₂, a₂, f₂, o₂⟩ => ?_
  refine WP.mono (shift16_ok (s₀ := s₀) (q := 0) (n := 80) (by decide) (by decide) l₂) fun s₃ ⟨w₃, l₃, _, f₃, o₃⟩ => ?_
  refine ⟨?_, l₃, f₃.trans (f₂.trans f₁), (o₁.trans o₂).trans o₃⟩
  rw [w₃, w₂, w₁, a₂ 0 (by decide), a₁ 1 (by decide), a₁ 0 (by decide), accs]
  ring

/-! ## A half -/

theorem exec_xop (o : XOp) (s : State) : exec (.xop o) s = some (o.exec s) := rfl

theorem save_ok {s₀ s : State} (hp : GPre s₀) (hc : s.gpr .edx = sP s₀) (hw : s.wr = s₀.wr) {a : Nat} (ha : a + 1 < 16) :
    WP isa (.block (Impl.Gcm.X86.save a)) s fun s' =>
      s'.mem.readW (sA s₀ a) 128 = s.xmm .xmm3 ∧ s'.mem.readW (sA s₀ (a + 1)) 128 = s.xmm .xmm5 ∧
      s'.xmm = s.xmm ∧ Stp s₀ [a, a + 1] s s' := by
  have o₁ := put_stp hp s (k := a) (by omega_arith) (s.xmm .xmm3)
  have o₂ := put_stp hp (put s₀ s a (s.xmm .xmm3)) (k := a + 1) ha (s.xmm .xmm5)
  apply WP.of_runBlock
  rw [Impl.Gcm.X86.save, runBlock_cons, st_exec hp hc hw (by omega_arith), runStep_some, runBlock_cons,
    st_exec hp (s := put s₀ s a (s.xmm .xmm3)) hc hw ha, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, put_read _ _, rfl, o₁.trans o₂⟩
  rw [o₂.slots a (by omega_arith) (by rw [List.mem_singleton]; omega_arith)]
  exact put_read _ _

theorem shift8_ok {s₀ s : State} {n : Nat} (hn : n ≤ 120) (hl : Low (s.xmm .xmm5) (n + 8)) :
    WP isa (.block Impl.Gcm.X86.shift8) s fun s' =>
      wide (s'.xmm .xmm3) (s'.xmm .xmm5) = x ^ 8 * wide (s.xmm .xmm3) (s.xmm .xmm5) ∧
      Low (s'.xmm .xmm5) n ∧ Stp s₀ [] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.shift8, runBlock_cons, runStep_some, exec, XOp.exec, isa, runBlock_nil, xmm_setXmm,
    reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left', eval_movdqa, psrldq1, pslldq15, pxor_eq]
  exact ⟨wide_shift (by decide) (hl.mono (by omega_arith)),
    low_xor (low_shr hl) ((low_shl _ _).mono (by omega_arith)), stp_vec⟩

theorem addSlot_ok {s₀ s : State} (hp : GPre s₀) (hc : s.gpr .edx = sP s₀) (hw : s.wr = s₀.wr) {k : Nat} (hk : k < 16)
    (r : XReg) (hr : r ≠ .xmm6) :
    WP isa (.block (Impl.Gcm.X86.addSlot r k)) s fun s' =>
      s'.xmm r = s.xmm r ^^^ s.mem.readW (sA s₀ k) 128 ∧ (∀ a, a ≠ r → a ≠ .xmm6 → s'.xmm a = s.xmm a) ∧
      Stp s₀ [] s s' := by
  apply WP.of_runBlock
  rw [Impl.Gcm.X86.addSlot, runBlock_cons, ld_exec hp hc hw hk, runStep_some]
  simp only [runBlock_cons, runStep_some, exec, XOp.exec, isa, runBlock_nil, xmm_setXmm, hr,
    ↓reduceIte, Option.some.injEq, exists_eq_left', pxor_eq]
  exact ⟨trivial, fun a h h' => by simp only [h, h', ite_false], stp_vec⟩

theorem addOdd_ok {s₀ s : State} (hp : GPre s₀) (hc : s.gpr .edx = sP s₀) (hw : s.wr = s₀.wr)
    (h5 : Low (s.xmm .xmm5) 80) (h9 : Low (s.mem.readW (sA s₀ 9) 128) 80) :
    WP isa (.block Impl.Gcm.X86.addOdd) s fun s' =>
      wide (s'.xmm .xmm3) (s'.xmm .xmm5) = x ^ 8 * wide (s.xmm .xmm3) (s.xmm .xmm5) +
        wide (s.mem.readW (sA s₀ 8) 128) (s.mem.readW (sA s₀ 9) 128) ∧
      Low (s'.xmm .xmm5) 72 ∧ Stp s₀ [] s s' := by
  rw [Impl.Gcm.X86.addOdd, WP.block_append_iff]
  refine WP.mono (shift8_ok (s₀ := s₀) (n := 72) (by decide) h5) fun s₁ ⟨w₁, l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addSlot_ok hp (by rw [o₁.gpr]; exact hc) (o₁.wr.trans hw) (by decide) .xmm3 (by decide))
    fun s₂ ⟨v₂, x₂, o₂⟩ => ?_
  have o := o₁.trans o₂
  refine WP.mono (addSlot_ok hp (by rw [o.gpr]; exact hc) (o.wr.trans hw) (by decide) .xmm5 (by decide))
    fun s₃ ⟨v₃, x₃, o₃⟩ => ?_
  rw [x₃ .xmm3 (by decide) (by decide), v₂, v₃, x₂ .xmm5 (by decide) (by decide), o.slots 9 (by decide) List.not_mem_nil,
    o₁.slots 8 (by decide) List.not_mem_nil, wide_xor, w₁]
  exact ⟨rfl, low_xor l₁ (h9.mono (by decide)), o.trans o₃⟩

/-- The polynomial of the half whose duplicated words are `d`. -/
noncomputable def hsum (d : BitVec 128) : Q :=
  accs (fun q => bits d (3 - q) 0 8) + x ^ 8 * accs (fun q => bits d (3 - q) 8 8)

theorem accs_mul (a : Nat → Q) (h : Q) : accs (fun q => a q * h) = accs a * h := by
  simp only [accs]; ring

theorem GInv.accs {s₀ t s : State} {d : BitVec 128} {k n : Nat} (h : GInv s₀ t d k n s) :
    accs (fun q => φ (s.xmm (Impl.Gcm.X86.acc q))) = accs (fun q => bits d (3 - q) k n) * φ (H s₀) := by
  rw [← accs_mul]
  simp only [Sse2.accs, h.acc 0 (by decide), h.acc 1 (by decide), h.acc 2 (by decide), h.acc 3 (by decide)]

theorem half_ok {s₀ s : State} (hp : GPre s₀) {d : BitVec 128} (hd : Dup d) (h : Mid s₀ s d 0) :
    WP isa (.block Impl.Gcm.X86.half) s fun s' =>
      wide (s'.xmm .xmm3) (s'.xmm .xmm5) = hsum d * φ (H s₀) ∧ Low (s'.xmm .xmm5) 72 ∧ Stp s₀ [8, 9] s s' := by
  rw [Impl.Gcm.X86.half, WP.block_append_iff]
  refine WP.mono (group_ok hp hd (by decide) h) fun s₁ g₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (horner_ok (s₀ := s₀)) fun s₂ ⟨w₂, l₂, f₂, o₂⟩ => ?_
  have m₂ := g₁.mid.next o₂ (f₂.trans g₁.mid.words)
  rw [WP.block_append_iff]
  refine WP.mono (save_ok hp m₂.edx m₂.wr (a := 8) (by decide)) fun s₃ ⟨z₃, v₃, x₃, o₃⟩ => ?_
  have m₃ : Mid s₀ s₃ d 8 := ⟨by rw [o₃.gpr]; exact m₂.edx, o₃.wr.trans m₂.wr,
    o₃.tab (by decide) m₂.tab, by rw [x₃]; exact m₂.words⟩
  rw [WP.block_append_iff]
  refine WP.mono (group_ok hp hd (by decide) m₃) fun s₄ g₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (horner_ok (s₀ := s₀)) fun s₅ ⟨w₅, l₅, f₅, o₅⟩ => ?_
  have o₄₅ := g₄.stp.trans o₅
  have m₅ := g₄.mid.next o₅ (f₅.trans g₄.mid.words)
  have z₅ : s₅.mem.readW (sA s₀ 8) 128 = s₂.xmm .xmm3 := (o₄₅.slots 8 (by decide) (List.not_mem_nil)).trans z₃
  have v₅ : s₅.mem.readW (sA s₀ 9) 128 = s₂.xmm .xmm5 := (o₄₅.slots 9 (by decide) (List.not_mem_nil)).trans v₃
  refine WP.mono (addOdd_ok hp m₅.edx m₅.wr l₅ (by rw [v₅]; exact l₂)) fun s₆ ⟨w₆, l₆, o₆⟩ => ⟨?_, l₆, ?_⟩
  · rw [w₆, w₅, g₄.accs, z₅, v₅, w₂, g₁.accs, hsum]
    ring
  · exact (((g₁.stp.trans o₂).trans o₃).trans o₄₅).trans o₆

/-! ## The bits of a block -/

/-- The word `w` of `v`, as a polynomial. -/
noncomputable def wsum (v : BitVec 128) (w : Nat) : Q :=
  ∑ k ∈ Finset.range 16, if (word v w).getLsbD (15 - k) then x ^ k else 0

theorem sum_blocks (f : Nat → Q) (m n : Nat) :
    ∑ i ∈ Finset.range (m * n), f i = ∑ p ∈ Finset.range m, ∑ k ∈ Finset.range n, f (n * p + k) := by
  induction m with
  | zero => rw [Nat.zero_mul, Finset.sum_range_zero, Finset.sum_range_zero]
  | succ m ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ, Nat.mul_comm n m]

theorem φ_words (v : BitVec 128) : φ v = ∑ p ∈ Finset.range 8, x ^ (16 * p) * wsum v (7 - p) := by
  rw [φ_eq]
  refine (sum_blocks _ 8 16).trans ?_
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_range] at hp
  rw [wsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have e : v.getMsbD (16 * p + k) = (word v (7 - p)).getLsbD (15 - k) := by
    rw [getLsbD_word _ _ _ (by omega_arith), BitVec.getMsbD, decide_eq_true (by omega_arith), Bool.true_and]
    exact congrArg _ (by omega_arith)
  rw [e]
  cases (word v (7 - p)).getLsbD (15 - k)
  · exact (mul_zero _).symm
  · exact pow_add _ _ _

theorem bits_16 (d : BitVec 128) (l : Nat) : bits d l 0 8 + x ^ 8 * bits d l 8 8 = wsum d (2 * l) := by
  rw [wsum, bits, bits, Finset.mul_sum]
  refine Eq.symm ((Finset.sum_range_add _ 8 8).trans (Eq.symm ?_))
  refine congrArg₂ _ (Finset.sum_congr rfl fun i _ => by rw [bitOf, Nat.zero_add]) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bitOf]
  cases (word d (2 * l)).getLsbD (15 - (8 + i))
  · exact mul_zero _
  · exact (pow_add _ _ _).symm

theorem hsum_eq (d : BitVec 128) :
    hsum d = wsum d 6 + x ^ 16 * wsum d 4 + x ^ 32 * wsum d 2 + x ^ 48 * wsum d 0 := by
  have e3 : _ = wsum d 6 := bits_16 d 3
  have e2 : _ = wsum d 4 := bits_16 d 2
  have e1 : _ = wsum d 2 := bits_16 d 1
  have e0 : _ = wsum d 0 := bits_16 d 0
  rw [← e3, ← e2, ← e1, ← e0, hsum]
  simp only [accs, Nat.sub_zero, Nat.reduceSub]
  ring

theorem wsum_congr {v v' : BitVec 128} {w w' : Nat} (h : word v w = word v' w') : wsum v w = wsum v' w' := by
  rw [wsum, wsum, h]

theorem dup_lo (v : BitVec 128) : Dup (XBinOp.eval .punpcklwd v v) := fun l hl => by
  rw [word_punpcklwd _ _ (by omega_arith), word_punpcklwd _ _ (by omega_arith)]
  simp (disch := omega) only [ite_eq_left, ite_eq_right]
  exact congrArg _ (by omega_arith)

theorem dup_hi (v : BitVec 128) : Dup (XBinOp.eval .punpckhwd v v) := fun l hl => by
  rw [word_punpckhwd _ _ (by omega_arith), word_punpckhwd _ _ (by omega_arith)]
  simp (disch := omega) only [ite_eq_left, ite_eq_right]
  exact congrArg _ (by omega_arith)

theorem hsum_lo (v : BitVec 128) : hsum (XBinOp.eval .punpcklwd v v) =
    wsum v 3 + x ^ 16 * wsum v 2 + x ^ 32 * wsum v 1 + x ^ 48 * wsum v 0 := by
  rw [hsum_eq, wsum_congr (word_punpcklwd v v (i := 6) (by decide)), wsum_congr (word_punpcklwd v v (i := 4) (by decide)),
    wsum_congr (word_punpcklwd v v (i := 2) (by decide)), wsum_congr (word_punpcklwd v v (i := 0) (by decide))]

theorem hsum_hi (v : BitVec 128) : hsum (XBinOp.eval .punpckhwd v v) =
    wsum v 7 + x ^ 16 * wsum v 6 + x ^ 32 * wsum v 5 + x ^ 48 * wsum v 4 := by
  rw [hsum_eq, wsum_congr (word_punpckhwd v v (i := 6) (by decide)), wsum_congr (word_punpckhwd v v (i := 4) (by decide)),
    wsum_congr (word_punpckhwd v v (i := 2) (by decide)), wsum_congr (word_punpckhwd v v (i := 0) (by decide))]

theorem φ_halves (v : BitVec 128) :
    φ v = hsum (XBinOp.eval .punpckhwd v v) + x ^ 64 * hsum (XBinOp.eval .punpcklwd v v) := by
  rw [φ_words, hsum_hi, hsum_lo]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.mul_zero, pow_zero, one_mul, Nat.reduceMul,
    Nat.sub_zero, Nat.reduceSub]
  ring

/-! ## A block -/

theorem addLow_ok {s₀ s : State} (hp : GPre s₀) (hc : s.gpr .edx = sP s₀) (hw : s.wr = s₀.wr)
    (h5 : Low (s.xmm .xmm5) 8) (h12 : Low (s.mem.readW (sA s₀ 12) 128) 72) :
    WP isa (.block Impl.Gcm.X86.addLow) s fun s' =>
      wide (s'.xmm .xmm3) (s'.xmm .xmm5) = wide (s.xmm .xmm3) (s.xmm .xmm5) +
        x ^ 64 * wide (s.mem.readW (sA s₀ 11) 128) (s.mem.readW (sA s₀ 12) 128) ∧
      Low (s'.xmm .xmm5) 8 ∧ Stp s₀ [] s s' := by
  apply WP.of_runBlock
  rw [Impl.Gcm.X86.addLow, runBlock_cons, ld_exec hp hc hw (by decide), runStep_some, runBlock_cons,
    ld_exec hp (by rw [gpr_setXmm]; exact hc) (by rw [wr_setXmm]; exact hw) (by decide), runStep_some]
  simp only [runBlock_cons, runStep_some, exec, XOp.exec, isa, runBlock_nil, xmm_setXmm, mem_setXmm,
    reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left', eval_movdqa, psrldq8, pslldq8, pxor_eq]
  refine ⟨?_, low_xor (low_xor h5 ((low_shl _ _).mono (by decide))) (low_shr h12), stp_vec⟩
  rw [BitVec.xor_assoc (s.xmm .xmm5), BitVec.xor_comm (_ <<< _), wide_xor,
    wide_shift (by decide) (h12.mono (by decide))]

theorem reduce_ok {s₀ s : State} (h5 : Low (s.xmm .xmm5) 8) :
    WP isa (.block Impl.Gcm.X86.reduce) s fun s' =>
      φ (s'.xmm .xmm3) = wide (s.xmm .xmm3) (s.xmm .xmm5) ∧ Stp s₀ [] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.reduce, runBlock_cons, runStep_some, exec, XOp.exec, isa, runBlock_nil, xmm_setXmm,
    reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left', eval_movdqa, pxor_eq]
  exact ⟨φ_reduceV h5, stp_vec⟩

theorem low_ok {s₀ s : State} (hp : GPre s₀) (hc : s.gpr .edx = sP s₀) (hw : s.wr = s₀.wr) (ht : Tab s₀ s.mem) :
    WP isa (.block Impl.Gcm.X86.low) s fun s' =>
      wide (s'.mem.readW (sA s₀ 11) 128) (s'.mem.readW (sA s₀ 12) 128) =
        hsum (XBinOp.eval .punpcklwd (s.xmm .xmm4) (s.xmm .xmm4)) * φ (H s₀) ∧
      Low (s'.mem.readW (sA s₀ 12) 128) 72 ∧ Stp s₀ [8, 9, 11, 12] s s' := by
  rw [Impl.Gcm.X86.low, WP.block_append_iff]
  refine WP.of_runBlock ⟨s.setXmm .xmm4 (XBinOp.eval .punpcklwd (s.xmm .xmm4) (s.xmm .xmm4)), rfl, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (half_ok hp (dup_lo (s.xmm .xmm4)) ⟨by rw [gpr_setXmm]; exact hc, by rw [wr_setXmm]; exact hw,
    by rw [mem_setXmm]; exact ht, by rw [xmm_setXmm_self, shlW_zero]⟩) fun s₁ ⟨w₁, l₁, o₁⟩ => ?_
  refine WP.mono (save_ok hp (by rw [o₁.gpr]; exact hc) (o₁.wr.trans hw) (a := 11) (by decide))
    fun s₂ ⟨z₂, v₂, _, o₂⟩ => ?_
  rw [z₂, v₂]
  exact ⟨w₁, l₁, (Stp.trans (s' := s.setXmm .xmm4 _) stp_vec o₁).trans o₂⟩

theorem high_ok {s₀ s : State} (hp : GPre s₀) (hc : s.gpr .edx = sP s₀) (hw : s.wr = s₀.wr) (ht : Tab s₀ s.mem)
    (h12 : Low (s.mem.readW (sA s₀ 12) 128) 72) :
    WP isa (.block Impl.Gcm.X86.high) s fun s' =>
      wide (s'.xmm .xmm3) (s'.xmm .xmm5) =
        hsum (XBinOp.eval .punpckhwd (s.mem.readW (sA s₀ 10) 128) (s.mem.readW (sA s₀ 10) 128)) * φ (H s₀) +
        x ^ 64 * wide (s.mem.readW (sA s₀ 11) 128) (s.mem.readW (sA s₀ 12) 128) ∧
      Low (s'.xmm .xmm5) 8 ∧ Stp s₀ [8, 9] s s' := by
  rw [Impl.Gcm.X86.high, WP.block_append_iff]
  apply WP.of_runBlock
  rw [runBlock_cons, ld_exec hp hc hw (by decide), runStep_some, runBlock_cons, exec_xop, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_⟩
  simp only [XOp.exec, xmm_setXmm_self]
  generalize s.mem.readW (sA s₀ 10) 128 = v
  have o₀ : Stp s₀ [] s ((s.setXmm .xmm4 v).setXmm .xmm4 (XBinOp.eval .punpckhwd v v)) := stp_vec
  generalize hs : (s.setXmm .xmm4 v).setXmm .xmm4 (XBinOp.eval .punpckhwd v v) = s₁ at o₀ ⊢
  have e₁ : s₁.xmm .xmm4 = shlW (XBinOp.eval .punpckhwd v v) 0 := by rw [← hs, xmm_setXmm_self, shlW_zero]
  rw [WP.block_append_iff]
  refine WP.mono (half_ok hp (dup_hi v) ⟨by rw [o₀.gpr]; exact hc, o₀.wr.trans hw,
    o₀.tab (fun _ _ => List.not_mem_nil) ht, e₁⟩) fun s₂ ⟨w₂, l₂, o₂⟩ => ?_
  have o := o₀.trans o₂
  refine WP.mono (addLow_ok hp (by rw [o.gpr]; exact hc) (o.wr.trans hw) (l₂.mono (by decide))
    (by rw [o.slots 12 (by decide) (by decide)]; exact h12)) fun s₃ ⟨w₃, l₃, o₃⟩ => ⟨?_, l₃, o.trans o₃⟩
  rw [w₃, w₂, o.slots 11 (by decide) (by decide), o.slots 12 (by decide) (by decide)]

theorem swap_ok {s₀ s : State} {r t k : XReg} (hrt : r ≠ t) (hrk : r ≠ k) (htk : t ≠ k) (hk : s.xmm k = lowB) :
    WP isa (.block (Impl.Gcm.X86.swap r t k)) s fun s' =>
      s'.xmm r = XBinOp.eval .pshufb (s.xmm r) revMask ∧ (∀ a, a ≠ r → a ≠ t → s'.xmm a = s.xmm a) ∧
      s'.mem = s.mem ∧ Stp s₀ [] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.swap, runBlock_cons, runStep_some, exec, XOp.exec, isa, runBlock_nil, xmm_setXmm,
    hrt, hrt.symm, hrk.symm, htk.symm, ↓reduceIte, Option.some.injEq, exists_eq_left', eval_movdqa, hk]
  exact ⟨swapV_eq _, fun a h h' => by simp only [h, h', ite_false], by simp only [mem_setXmm], stp_vec⟩

/-! ## The loop -/

/-- `s` is `s₀` but for the scratch buffer and the registers that are not
callee-saved, and `swap`'s constant is in its slot. -/
structure Base (s₀ s : State) : Prop where
  frame : Frame [sR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r

theorem Base.refl (s : State) : Base s s := ⟨Frame.refl _ _, rfl, rfl, fun _ _ => rfl⟩

theorem Base.sp {s₀ s : State} (h : Base s₀ s) : s.gpr .esp = s₀.gpr .esp := h.saved .esp (by decide)

theorem Base.stp {s₀ s s' : State} {ks : List Nat} (h : Base s₀ s) (o : Stp s₀ ks s s') : Base s₀ s' :=
  ⟨h.frame.trans o.frame, o.rd.trans h.rd, o.wr.trans h.wr, fun r hr => by rw [o.gpr]; exact h.saved r hr⟩

theorem Base.setReg {s₀ s : State} (h : Base s₀ s) {r : Reg} (v : BitVec 32) (hr : r ∉ calleeSaved) :
    Base s₀ (s.setReg r v) :=
  ⟨by rw [mem_setReg]; exact h.frame, by rw [rd_setReg]; exact h.rd, by rw [wr_setReg]; exact h.wr, fun a ha => by
    rw [gpr_setReg_of_ne _ _ (show a ≠ r from fun e => hr (e ▸ ha))]; exact h.saved a ha⟩

/-- An argument's load. -/
theorem Base.arg {s₀ s : State} (h : Base s₀ s) (hp : GPre s₀) {i : Nat} (hi : i < 5) (d : Reg) :
    exec (.mov d (.mem (Impl.Gcm.X86.argOp i))) s = some (s.setReg d (arg s₀ i)) := by
  have hin : (aR s₀).Contains (argAddr s₀ i) 4 :=
    Proof.Aes.X86.part_contains (N := 24) (a := 4) (k := 20) hp.fSp (by decide) (by omega_arith) (by omega_arith) (by decide)
  have he : s.ea (Impl.Gcm.X86.argOp i) = argAddr s₀ i := by
    simp only [State.ea, Impl.Gcm.X86.argOp, Impl.Gcm.X86.at_, argAddr, h.sp]
  have hr : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
    rw [h.rd, h.wr, hp.rd]
    exact ⟨aR s₀, by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or], hin⟩
  have hm : s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i :=
    h.frame.readW (r := aR s₀) hin (fun r' hr' => by rw [List.mem_singleton.mp hr']; exact hp.aS) (by decide)
  simp only [exec, readSrc, State.load32, he, hr, ite_true, hm, Option.map_some]

/-- A block outside the scratch buffer is what it was. -/
theorem Base.block_eq {s₀ s : State} (h : Base s₀ s) {p : Addr} (hd : (⟨p, 16⟩ : Region).Disjoint (sR s₀)) :
    blockAt s.mem p = blockAt s₀.mem p :=
  Proof.Gcm.blockAt_congr fun _ hi => h.frame.bytes (R := ⟨p, 16⟩)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (show (16 : Nat) ≤ 2 ^ 64 by decide) hi

/-- The block `j` of the data. -/
abbrev blk (s₀ : State) (j : Nat) : Block := blockAt s₀.mem ((dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j))

theorem Base.data_eq {s₀ s : State} (h : Base s₀ s) (hp : GPre s₀) {j : Nat} (hj : j < nBlk s₀) :
    blockAt s.mem ((dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j)) = blk s₀ j := by
  have hd := hp.fD
  refine Proof.Gcm.blockAt_congr fun k hk => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h.frame.bytes (R := ⟨(dP s₀).setWidth 64, 16 * nBlk s₀⟩)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.dDS)
    (by show 16 * nBlk s₀ ≤ 2 ^ 64; omega_using [hd])
    (by show 16 * j + k < 16 * nBlk s₀; omega_using [hj, hk])

/-- `Y` after `i` blocks. -/
abbrev Y (s₀ : State) (i : Nat) : Block :=
  Spec.Gcm.ghashFrom (H s₀) (blockAt s₀.mem ((yP s₀).setWidth 64)) (Spec.Gcm.blocksAt s₀.mem ((dP s₀).setWidth 64) i)

/-- Before block `i`. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  base : Base s₀ s
  edx : s.gpr .edx = sP s₀
  count : s.gpr .ecx = BitVec.ofNat 32 (nBlk s₀ - i)
  data : s.gpr .eax = dP s₀ + BitVec.ofNat 32 (16 * i)
  low : s.xmm .xmm7 = lowB
  slot : s.mem.readW (sA s₀ 13) 128 = lowB
  tab : Tab s₀ s.mem
  acc : s.xmm .xmm3 = Y s₀ i

theorem loadX_ok {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : Inv s₀ i s) (hb : i < nBlk s₀) :
    WP isa (.block Impl.Gcm.X86.loadX) s fun s' =>
      s'.xmm .xmm4 = blk s₀ i ^^^ Y s₀ i ∧ s'.mem.readW (sA s₀ 10) 128 = blk s₀ i ^^^ Y s₀ i ∧ Stp s₀ [10] s s' := by
  have hf := hp.fD
  have he : s.ea (Impl.Gcm.X86.at_ .eax 0) = (dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i) := by
    simp only [State.ea, Impl.Gcm.X86.at_, hi.data, BitVec.add_zero]
    exact addr_eq (by omega_using [hb, hf])
  have hin : InRegions (s.rd ++ s.wr) ((dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) 16 := by
    rw [hi.base.rd, hi.base.wr, hp.rd]
    refine ⟨dR s₀, ?_, Offset.contains_base _ (by omega_using [hb]) (by omega_using [hb, hf])⟩
    simp only [List.mem_append, List.mem_cons, or_true, true_or]
  rw [Impl.Gcm.X86.loadX, WP.block_append_iff]
  refine WP.of_runBlock ⟨s.setXmm .xmm4 (s.mem.readW ((dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) 128), ?_, ?_⟩
  · rw [runBlock_cons]
    simp only [exec, State.load128, he, hin, ite_true, Option.map_some, runStep_some, runBlock_nil]
  have o₀ : Stp s₀ [] s (s.setXmm .xmm4 (s.mem.readW ((dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) 128)) := stp_vec
  rw [WP.block_append_iff]
  refine WP.mono (swap_ok (s₀ := s₀) (r := .xmm4) (t := .xmm5) (k := .xmm7) (by decide) (by decide) (by decide)
    (by rw [xmm_setXmm_of_ne _ _ (by decide)]; exact hi.low)) fun s₁ ⟨v₁, x₁, _, o₁⟩ => ?_
  rw [xmm_setXmm_self, ← VG.Proof.Gcm.X86.blockAt_eq, hi.base.data_eq hp hb] at v₁
  have y₁ : s₁.xmm .xmm3 = Y s₀ i := by
    rw [x₁ .xmm3 (by decide) (by decide), xmm_setXmm_of_ne _ _ (by decide)]; exact hi.acc
  have o := o₀.trans o₁
  have o₂ : Stp s₀ [] s₁ (s₁.setXmm .xmm4 (blk s₀ i ^^^ Y s₀ i)) := stp_vec
  apply WP.of_runBlock
  rw [runBlock_cons, exec_xop, runStep_some]
  simp only [XOp.exec, pxor_eq, v₁, y₁]
  rw [runBlock_cons, st_exec hp (by rw [gpr_setXmm, o.gpr]; exact hi.edx)
    (by rw [wr_setXmm]; exact o.wr.trans hi.base.wr) (by decide), runStep_some, runBlock_nil]
  refine ⟨_, rfl, xmm_setXmm_self s₁ .xmm4 _, ?_, (o.trans o₂).trans (put_stp hp _ (by decide) _)⟩
  rw [put_read, xmm_setXmm_self]

theorem next_ok {s₀ s : State} (hp : GPre s₀) (hc : s.gpr .edx = sP s₀) (hw : s.wr = s₀.wr) :
    WP isa (.block Impl.Gcm.X86.next) s fun s' =>
      s'.xmm .xmm7 = s.mem.readW (sA s₀ 13) 128 ∧ s'.xmm .xmm3 = s.xmm .xmm3 ∧
      s'.gpr .eax = s.gpr .eax + 16 ∧ s'.gpr .ecx = s.gpr .ecx - 1 ∧ s'.zf = some (s.gpr .ecx - 1 == 0) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  rw [Impl.Gcm.X86.next, runBlock_cons, ld_exec hp hc hw (by decide), runStep_some]
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags, gpr_setXmm, mem_setReg, mem_arithFlags,
    mem_setXmm, rd_setReg, rd_arithFlags, rd_setXmm, wr_setReg, wr_arithFlags, wr_setXmm, xmm_setReg, xmm_arithFlags,
    xmm_setXmm, Option.some.injEq, exists_eq_left', true_and, and_true]
  exact ⟨rfl, fun r h h' => by simp only [h, h', ite_false]⟩

theorem φ_Y_succ (s₀ : State) (i : Nat) : φ (Y s₀ (i + 1)) = φ (blk s₀ i ^^^ Y s₀ i) * φ (H s₀) := by
  rw [show Y s₀ (i + 1) = Spec.Gcm.mul (Y s₀ i ^^^ blk s₀ i) (H s₀) from
    Proof.Gcm.ghashFrom_blocksAt_succ _ _ _ _ _, φ_mul, BitVec.xor_comm]

theorem body_ok {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : Inv s₀ i s) (hb : i < nBlk s₀) :
    WP isa (.block Impl.Gcm.X86.body) s fun s' =>
      Inv s₀ (i + 1) s' ∧ s'.zf = some (decide (nBlk s₀ - (i + 1) = 0)) := by
  rw [Impl.Gcm.X86.body, WP.block_append_iff]
  refine WP.mono (loadX_ok hp hi hb) fun s₁ ⟨x₁, m₁, o₁⟩ => ?_
  have c₁ : s₁.gpr .edx = sP s₀ := by rw [o₁.gpr]; exact hi.edx
  have t₁ : Tab s₀ s₁.mem := o₁.tab (by decide) hi.tab
  rw [WP.block_append_iff]
  refine WP.mono (low_ok hp c₁ (o₁.wr.trans hi.base.wr) t₁) fun s₂ ⟨w₂, l₂, o₂⟩ => ?_
  have c₂ : s₂.gpr .edx = sP s₀ := by rw [o₂.gpr]; exact c₁
  have w₁₂ := o₂.wr.trans (o₁.wr.trans hi.base.wr)
  rw [WP.block_append_iff]
  refine WP.mono (high_ok hp c₂ w₁₂ (o₂.tab (by decide) t₁) l₂) fun s₃ ⟨w₃, l₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok (s₀ := s₀) l₃) fun s₄ ⟨v₄, o₄⟩ => ?_
  have o := ((o₁.trans o₂).trans o₃).trans o₄
  have acc₄ : s₄.xmm .xmm3 = Y s₀ (i + 1) := by
    apply φ_inj
    rw [v₄, w₃, w₂, x₁, o₂.slots 10 (by decide) (by decide), m₁, φ_Y_succ, φ_halves (blk s₀ i ^^^ Y s₀ i)]
    ring
  have b₄ := hi.base.stp o
  refine WP.mono (next_ok hp (by rw [o.gpr]; exact hi.edx) b₄.wr)
    fun s₅ ⟨x7, x3, eax, ecx, zf, regs, mem, rd, wr⟩ => ?_
  have bound : nBlk s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  have cnt : s₄.gpr .ecx - 1 = BitVec.ofNat 32 (nBlk s₀ - (i + 1)) := by
    rw [o.gpr, hi.count, Wp.ofNat_pred (by omega_using [hb]), Nat.sub_sub]
  have const : s₄.mem.readW (sA s₀ 13) 128 = lowB := (o.slots 13 (by decide) (by decide)).trans hi.slot
  refine ⟨⟨⟨by rw [mem]; exact b₄.frame, rd.trans b₄.rd, wr.trans b₄.wr, fun r hr => ?_⟩, ?_, ecx.trans cnt, ?_, x7.trans const,
    by rw [mem]; exact const, by rw [mem]; exact o.tab (by decide) hi.tab, x3.trans acc₄⟩, ?_⟩
  · have hn : r ≠ .eax ∧ r ≠ .ecx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [regs r hn.1 hn.2]; exact b₄.saved r hr
  · rw [regs _ (by decide) (by decide), o.gpr]; exact hi.edx
  · rw [eax, o.gpr, hi.data, BitVec.add_assoc]
    change dP s₀ + (BitVec.ofNat 32 (16 * i) + BitVec.ofNat 32 16) = _
    rw [← BitVec.ofNat_add, show 16 * i + 16 = 16 * (i + 1) by omega_using []]
  · rw [zf, cnt, Wp.ofNat_beq_zero (by omega_using [bound])]

theorem blocks_ok {s₀ s : State} (hp : GPre s₀) (hi : Inv s₀ 0 s) (hn : 0 < nBlk s₀) :
    WP isa (.loop (.block Impl.Gcm.X86.body) .ne) s (Inv s₀ (nBlk s₀)) := by
  refine WP.loop (M := isa) (fun k s => ∃ i, k = nBlk s₀ - i ∧ i < nBlk s₀ ∧ Inv s₀ i s)
    (fun k s ⟨i, hk, hb, hs⟩ => WP.mono (body_ok hp hs hb) fun s' ⟨inv, z⟩ => ?_)
    (nBlk s₀) s ⟨0, rfl, hn, hi⟩
  by_cases hl : i + 1 = nBlk s₀
  · refine .inl ⟨by simp [X86.eval, z, hl], ?_⟩
    rw [hl] at inv; exact inv
  · exact .inr ⟨by simp [X86.eval, z]; omega_using [hb, hl],
      nBlk s₀ - (i + 1), by omega_using [hk, hb], i + 1, rfl, by omega_using [hb, hl], inv⟩

/-! ## The setup -/

theorem count_ok {s₀ : State} (hp : GPre s₀) :
    WP isa (.block Impl.Gcm.X86.count) s₀ fun s =>
      Base s₀ s ∧ s.gpr .ecx = arg s₀ 3 ∧ s.zf = some (decide (nBlk s₀ = 0)) ∧ s.mem = s₀.mem := by
  apply WP.of_runBlock
  rw [Impl.Gcm.X86.count, runBlock_cons, (Base.refl s₀).arg hp (by decide), runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, ↓reduceIte, Option.some.injEq, exists_eq_left',
    BitVec.and_self]
  refine ⟨⟨by rw [mem_arithFlags, mem_setReg]; exact Frame.refl _ _, by rw [rd_arithFlags, rd_setReg],
    by rw [wr_arithFlags, wr_setReg], fun r hr => ?_⟩, trivial, ?_, trivial⟩
  · rw [gpr_arithFlags]
    exact ((Base.refl s₀).setReg (r := .ecx) _ (by decide)).saved r hr
  · rw [zf_arithFlags]
    refine congrArg some ?_
    have e := Wp.ofNat_beq_zero (arg s₀ 3).isLt
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at e
    exact e

theorem start_ok {s₀ s : State} (hp : GPre s₀) (hb : Base s₀ s) :
    WP isa (.block Impl.Gcm.X86.start) s fun s' =>
      Base s₀ s' ∧ s'.gpr .edx = sP s₀ ∧ s'.gpr .ecx = s.gpr .ecx ∧ s'.xmm .xmm7 = lowB ∧
      s'.mem.readW (sA s₀ 13) 128 = lowB := by
  rw [Impl.Gcm.X86.start, WP.block_append_iff]
  have first : WP isa (.block [.mov .edx (.mem (Impl.Gcm.X86.argOp 4)), .mov .eax (.imm Impl.Gcm.X86.lowBytes),
      .xop (.movd .xmm7 .eax), .xop (.pshufd .xmm7 .xmm7 0)]) s fun s' =>
      s'.xmm .xmm7 = lowB ∧ s'.gpr .edx = sP s₀ ∧ (∀ r, r ≠ .eax → r ≠ .edx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    apply WP.of_runBlock
    rw [runBlock_cons, hb.arg hp (by decide), runStep_some]
    simp only [runBlock_cons, runStep_some, exec, readSrc, Option.map_some, XOp.exec, isa, runBlock_nil,
      xmm_setXmm, gpr_setXmm, gpr_setReg, mem_setXmm, mem_setReg, rd_setXmm, rd_setReg, wr_setXmm, wr_setReg,
      reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left', true_and, and_true]
    exact ⟨rfl, fun r h h' => by simp only [h, h', ite_false]⟩
  refine WP.mono first fun s₁ ⟨x₁, d₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  have b₁ : Base s₀ s₁ := ⟨by rw [m₁]; exact hb.frame, rd₁.trans hb.rd, wr₁.trans hb.wr, fun r hr => by
    rw [g₁ r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)]; exact hb.saved r hr⟩
  apply WP.of_runBlock
  rw [runBlock_cons, st_exec hp d₁ b₁.wr (by decide), runStep_some, runBlock_nil]
  exact ⟨_, rfl, b₁.stp (put_stp hp _ (by decide) _), d₁, g₁ _ (by decide) (by decide), x₁, (put_read _ _).trans x₁⟩

theorem rMask_value : XBinOp.eval .punpckldq (XBinOp.eval .pxor ((0 : BitVec 96) ++ (0xe1000000 : BitVec 32))
      ((0 : BitVec 96) ++ (0xe1000000 : BitVec 32)))
    (XBinOp.eval .punpckldq ((0 : BitVec 96) ++ (0x80000000 : BitVec 32)) ((0 : BitVec 96) ++ (0xe1000000 : BitVec 32))) = rM := by
  decide +kernel

theorem rMask_ok (s : State) :
    WP isa (.block Impl.Gcm.X86.rMask) s fun s' =>
      s'.xmm .xmm2 = rM ∧ s'.xmm .xmm7 = s.xmm .xmm7 ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.rMask, runBlock_cons, runStep_some, exec, readSrc, Option.map_some, XOp.exec, isa, runBlock_nil,
    xmm_setXmm, xmm_setReg, gpr_setXmm, gpr_setReg, mem_setXmm, mem_setReg, rd_setXmm, rd_setReg, wr_setXmm, wr_setReg,
    reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left', rMask_value, true_and, and_true]
  exact fun r h => by simp only [h, ite_false]

/-- A change of `eax`, vector registers and nothing else. -/
theorem Base.vec {s₀ s s' : State} (h : Base s₀ s) (hg : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Base s₀ s' :=
  ⟨by rw [hm]; exact h.frame, hrd.trans h.rd, hwr.trans h.wr, fun r hr => by
    rw [hg r (by rintro rfl; revert hr; decide)]; exact h.saved r hr⟩

/-- A 16-byte buffer's load, from the pointer in an argument. -/
theorem ldArg_ok {s₀ s : State} (hp : GPre s₀) (hb : Base s₀ s) {i : Nat} (hi : i < 5) (r : XReg)
    (hin : InRegions (s₀.rd ++ s₀.wr) ((arg s₀ i).setWidth 64) 16)
    (hd : (⟨(arg s₀ i).setWidth 64, 16⟩ : Region).Disjoint (sR s₀)) :
    WP isa (.block [.mov .eax (.mem (Impl.Gcm.X86.argOp i)), .movdquLoad r (Impl.Gcm.X86.at_ .eax 0)]) s fun s' =>
      XBinOp.eval .pshufb (s'.xmm r) revMask = blockAt s₀.mem ((arg s₀ i).setWidth 64) ∧
      (∀ a, a ≠ r → s'.xmm a = s.xmm a) ∧ (∀ a, a ≠ .eax → s'.gpr a = s.gpr a) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  rw [runBlock_cons, hb.arg hp hi, runStep_some, runBlock_cons]
  have he : (s.setReg .eax (arg s₀ i)).ea (Impl.Gcm.X86.at_ .eax 0) = (arg s₀ i).setWidth 64 := by
    simp only [State.ea, Impl.Gcm.X86.at_, gpr_setReg_self, BitVec.add_zero]
  have hin' : InRegions ((s.setReg .eax (arg s₀ i)).rd ++ (s.setReg .eax (arg s₀ i)).wr) ((arg s₀ i).setWidth 64) 16 := by
    rw [rd_setReg, wr_setReg, hb.rd, hb.wr]; exact hin
  simp only [exec, State.load128, he, hin', ite_true, Option.map_some, runStep_some, runBlock_nil, Option.some.injEq,
    exists_eq_left']
  simp only [xmm_setXmm, mem_setReg, gpr_setXmm, gpr_setReg, mem_setXmm, rd_setXmm, rd_setReg, wr_setXmm, wr_setReg,
    xmm_setReg, and_true, ↓reduceIte]
  refine ⟨?_, fun a h => by simp only [h, ite_false], fun a h => by simp only [h, ite_false]⟩
  rw [← VG.Proof.Gcm.X86.blockAt_eq]; exact hb.block_eq hd

theorem loadH_ok {s₀ s : State} (hp : GPre s₀) (hb : Base s₀ s) (h7 : s.xmm .xmm7 = lowB) :
    WP isa (.block Impl.Gcm.X86.loadH) s fun s' =>
      s'.xmm .xmm0 = H s₀ ∧ (∀ a, a ≠ .xmm0 → a ≠ .xmm1 → s'.xmm a = s.xmm a) ∧
      (∀ a, a ≠ .eax → s'.gpr a = s.gpr a) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : InRegions (s₀.rd ++ s₀.wr) ((arg s₀ 0).setWidth 64) 16 :=
    ⟨hR s₀, by simp only [hp.rd, List.mem_append, List.mem_cons, true_or], Region.contains_self _ _⟩
  rw [Impl.Gcm.X86.loadH, WP.block_append_iff]
  refine WP.mono (ldArg_ok hp hb (by decide) .xmm0 hin hp.dHS) fun s₁ ⟨v₁, x₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (swap_ok (s₀ := s₀) (by decide) (by decide) (by decide) (by rw [x₁ _ (by decide)]; exact h7))
    fun s₂ ⟨v₂, x₂, m₂, o₂⟩ => ?_
  exact ⟨v₂.trans v₁, fun a h h' => (x₂ a h h').trans (x₁ a h), fun a h => by rw [o₂.gpr]; exact g₁ a h, m₂.trans m₁,
    o₂.rd.trans rd₁, o₂.wr.trans wr₁⟩

/-- The table's first `n` entries, and the next one. -/
structure TInv (s₀ t : State) (n : Nat) (s : State) : Prop where
  stp : Stp s₀ (List.range n) t s
  tab : ∀ j < n, φ (s.mem.readW (sA s₀ j) 128) = x ^ j * φ (H s₀)
  next : φ (s.xmm .xmm0) = x ^ n * φ (H s₀)
  mask : s.xmm .xmm2 = rM
  low : s.xmm .xmm7 = lowB

theorem mulX_ok {s₀ s : State} (h2 : s.xmm .xmm2 = rM) :
    WP isa (.block Impl.Gcm.X86.mulX) s fun s' =>
      φ (s'.xmm .xmm0) = x * φ (s.xmm .xmm0) ∧ s'.xmm .xmm2 = s.xmm .xmm2 ∧ s'.xmm .xmm7 = s.xmm .xmm7 ∧
      Stp s₀ [] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.mulX, runBlock_cons, runStep_some, exec, XOp.exec, isa, runBlock_nil, xmm_setXmm,
    reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left', eval_movdqa, h2]
  exact ⟨φ_mulXV _, trivial, trivial, stp_vec⟩

theorem entry_ok {s₀ t s : State} (hp : GPre s₀) (hc : t.gpr .edx = sP s₀) (hw : t.wr = s₀.wr) {n : Nat} (hn : n < 8)
    (h : TInv s₀ t n s) : WP isa (.block (Impl.Gcm.X86.entry n)) s (TInv s₀ t (n + 1)) := by
  have o₁ := put_stp hp s (k := n) (by omega_arith) (s.xmm .xmm0)
  have r₁ : (put s₀ s n (s.xmm .xmm0)).mem.readW (sA s₀ n) 128 = s.xmm .xmm0 := put_read _ _
  rw [Impl.Gcm.X86.entry]
  refine WP.block_cons_iff.mpr ⟨_, st_exec hp (by rw [h.stp.gpr]; exact hc) (h.stp.wr.trans hw) (by omega_arith) _, ?_⟩
  refine WP.mono (mulX_ok (s₀ := s₀) h.mask) fun s₂ ⟨v₂, m₂, l₂, o₂⟩ => ?_
  have r₂ : s₂.mem.readW (sA s₀ n) 128 = s.xmm .xmm0 := (o₂.slots n (by omega_arith) List.not_mem_nil).trans r₁
  refine ⟨?_, fun j hj => ?_, ?_, m₂.trans h.mask, l₂.trans h.low⟩
  · rw [List.range_succ]
    have := h.stp.trans (o₁.trans o₂)
    rwa [List.append_nil] at this
  · by_cases hjn : j = n
    · rw [hjn, r₂]; exact h.next
    · rw [(o₁.trans o₂).slots j (by omega_arith) (by simpa using hjn)]
      exact h.tab j (by omega_arith)
  · rw [v₂, pow_succ', mul_assoc]
    exact congrArg _ h.next

theorem table_ok {s₀ s : State} (hp : GPre s₀) (hc : s.gpr .edx = sP s₀) (hw : s.wr = s₀.wr) (h0 : s.xmm .xmm0 = H s₀)
    (h2 : s.xmm .xmm2 = rM) (h7 : s.xmm .xmm7 = lowB) : WP isa (.block Impl.Gcm.X86.table) s (TInv s₀ s 8) := by
  have all : ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap Impl.Gcm.X86.entry)) s (TInv s₀ s n) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact WP.block_nil ⟨Stp.of_eq rfl rfl rfl rfl, fun _ h => absurd h (Nat.not_lt_zero _),
        by rw [h0, pow_zero, one_mul], h2, h7⟩
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
      refine WP.mono (ih (by omega_arith)) fun s₂ h₂ => ?_
      rw [List.flatMap_singleton]
      exact entry_ok hp hc hw (by omega_arith) h₂
  exact all 8 (Nat.le_refl 8)

theorem loadY_ok {s₀ s : State} (hp : GPre s₀) (hb : Base s₀ s) (h7 : s.xmm .xmm7 = lowB) :
    WP isa (.block Impl.Gcm.X86.loadY) s fun s' =>
      s'.xmm .xmm3 = blockAt s₀.mem ((yP s₀).setWidth 64) ∧ s'.xmm .xmm7 = lowB ∧ s'.gpr .eax = dP s₀ ∧
      (∀ a, a ≠ .eax → s'.gpr a = s.gpr a) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : InRegions (s₀.rd ++ s₀.wr) ((arg s₀ 1).setWidth 64) 16 :=
    ⟨yR s₀, by simp only [hp.wr, List.mem_append, List.mem_cons, true_or, or_true], Region.contains_self _ _⟩
  rw [Impl.Gcm.X86.loadY, WP.block_append_iff]
  refine WP.mono (ldArg_ok hp hb (by decide) .xmm3 hin hp.dYS) fun s₁ ⟨v₁, x₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (swap_ok (s₀ := s₀) (by decide) (by decide) (by decide) (by rw [x₁ _ (by decide)]; exact h7))
    fun s₂ ⟨v₂, x₂, m₂, o₂⟩ => ?_
  have b₂ := (hb.vec g₁ m₁ rd₁ wr₁).stp o₂
  apply WP.of_runBlock
  rw [runBlock_cons, b₂.arg hp (by decide), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ?_, gpr_setReg_self _ _ _, fun a h => ?_, ?_, ?_, ?_⟩
  · rw [xmm_setReg, v₂]; exact v₁
  · rw [xmm_setReg, x₂ _ (by decide) (by decide), x₁ _ (by decide)]; exact h7
  · rw [gpr_setReg_of_ne _ _ h, o₂.gpr]; exact g₁ a h
  · rw [mem_setReg, m₂, m₁]
  · rw [rd_setReg, o₂.rd, rd₁]
  · rw [wr_setReg, o₂.wr, wr₁]

theorem setup_ok {s₀ s : State} (hp : GPre s₀) (hb : Base s₀ s) (hc : s.gpr .ecx = arg s₀ 3) :
    WP isa (.block Impl.Gcm.X86.setup) s (Inv s₀ 0) := by
  rw [Impl.Gcm.X86.setup, WP.block_append_iff]
  refine WP.mono (start_ok hp hb) fun s₁ ⟨b₁, d₁, c₁, l₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rMask_ok s₁) fun s₂ ⟨r₂, l₂, g₂, m₂, rd₂, wr₂⟩ => ?_
  have b₂ := b₁.vec g₂ m₂ rd₂ wr₂
  rw [WP.block_append_iff]
  refine WP.mono (loadH_ok hp b₂ (l₂.trans l₁)) fun s₃ ⟨h₃, x₃, g₃, m₃, rd₃, wr₃⟩ => ?_
  have b₃ := b₂.vec g₃ m₃ rd₃ wr₃
  have d₃ : s₃.gpr .edx = sP s₀ := by rw [g₃ _ (by decide), g₂ _ (by decide)]; exact d₁
  rw [WP.block_append_iff]
  refine WP.mono (table_ok hp d₃ b₃.wr h₃ (by rw [x₃ _ (by decide) (by decide)]; exact r₂)
    (by rw [x₃ _ (by decide) (by decide), l₂]; exact l₁)) fun s₄ t₄ => ?_
  refine WP.mono (loadY_ok hp (b₃.stp t₄.stp) t₄.low) fun s₅ ⟨y₅, l₅, e₅, g₅, m₅, rd₅, wr₅⟩ => ?_
  refine ⟨(b₃.stp t₄.stp).vec g₅ m₅ rd₅ wr₅, ?_, ?_, ?_, l₅, ?_, ?_, ?_⟩
  · rw [g₅ _ (by decide), t₄.stp.gpr]; exact d₃
  · rw [g₅ _ (by decide), t₄.stp.gpr, g₃ _ (by decide), g₂ _ (by decide), c₁, hc, Nat.sub_zero, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [e₅, Nat.mul_zero, BitVec.add_zero]
  · rw [m₅, t₄.stp.slots 13 (by decide) (by decide), m₃, m₂]; exact k₁
  · rw [m₅]; exact t₄.tab
  · rw [y₅]; exact (Proof.Gcm.ghashFrom_blocksAt_zero _ _ _ _).symm

/-! ## The whole function -/

theorem finish_ok {s₀ s : State} (hp : GPre s₀) (hi : Inv s₀ (nBlk s₀) s) :
    WP isa (.block Impl.Gcm.X86.finish) s fun s' => abiPreserved s₀ s' ∧ Proof.Gcm.ghashX86.post s₀ s' := by
  rw [Impl.Gcm.X86.finish, WP.block_append_iff]
  refine WP.mono (swap_ok (s₀ := s₀) (by decide) (by decide) (by decide) hi.low) fun s₁ ⟨v₁, _, _, o₁⟩ => ?_
  have b₁ := hi.base.stp o₁
  have b₂ := b₁.setReg (r := .eax) (arg s₀ 1) (by decide)
  have x₂ : (s₁.setReg .eax (arg s₀ 1)).xmm .xmm3 = XBinOp.eval .pshufb (Y s₀ (nBlk s₀)) revMask := by
    rw [xmm_setReg, v₁, hi.acc]
  have he : (s₁.setReg .eax (arg s₀ 1)).ea (Impl.Gcm.X86.at_ .eax 0) = (yP s₀).setWidth 64 := by
    simp only [State.ea, Impl.Gcm.X86.at_, gpr_setReg_self, BitVec.add_zero]
  apply WP.of_runBlock
  rw [runBlock_cons, b₁.arg hp (by decide), runStep_some]
  generalize s₁.setReg .eax (arg s₀ 1) = s₂ at b₂ x₂ he ⊢
  have hw : InRegions s₂.wr ((yP s₀).setWidth 64) 16 := by
    rw [b₂.wr, hp.wr]
    exact ⟨yR s₀, List.mem_cons_self, Region.contains_self _ _⟩
  rw [runBlock_cons]
  simp only [exec, State.store128, he, hw, ite_true, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', x₂]
  refine ⟨⟨b₂.saved, ?_⟩, ?_⟩
  · show (s₂.mem.writeW _ _).readW _ 32 = _
    rw [Mem.readW_writeW_sep (hp.rY.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
    exact b₂.frame.readW (r := rR s₀) (Region.contains_self _ _)
      (fun r' hr' => by rw [List.mem_singleton.mp hr']; exact hp.rS) (by decide)
  · exact VG.Proof.Gcm.X86.blockAt_store _ _ _

theorem gh_correct (s₀ : State) (hp : GPre s₀) :
    WP isa Impl.Gcm.X86.ghash s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Gcm.ghashX86.post s₀ s' := by
  unfold Impl.Gcm.X86.ghash
  refine WP.seq (WP.mono (count_ok hp) fun s ⟨hb, hc, z, hm⟩ => ?_)
  refine WP.ite (decide (nBlk s₀ = 0)) (by simp only [X86.eval, z]) (fun h => ?_) (fun h => ?_)
  · have h0 : (arg s₀ 3).toNat = 0 := of_decide_eq_true h
    refine WP.block_nil ⟨⟨hb.saved, ?_⟩, ?_⟩
    · rw [hm]
    · simp only [Proof.Gcm.ghashX86, h0, hm]; rfl
  · have hn : 0 < nBlk s₀ := Nat.pos_of_ne_zero (of_decide_eq_false h)
    refine WP.seq (WP.mono (setup_ok hp hb hc) fun s₁ hi => ?_)
    exact WP.seq (WP.mono (blocks_ok hp hi hn) fun s₂ h₂ => finish_ok hp h₂)

end VG.Proof.Gcm.X86.Sse2

end

/-! ## Constant time, and the contract -/

public section

namespace VG.Impl.Gcm.X86
materialize_code ghash
end VG.Impl.Gcm.X86

namespace VG.Proof.Gcm.X86

open VG VG.X86

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashX86.pre Proof.Gcm.ghashX86.pub Impl.Gcm.X86.ghash :=
  VG.Taint.constantTime (A := sseTaint) ghτ₀ (fun _ _ h₁ h₂ hp => gh_agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem ghash_correct (s : State) (hs : Proof.Gcm.ghashX86.pre s) :
    ∃ t s', Exec isa Impl.Gcm.X86.ghash s t s' ∧ abiPreserved s s' ∧ Proof.Gcm.ghashX86.post s s' :=
  Sse2.gh_correct s (GPre.of hs)

end VG.Proof.Gcm.X86

end
