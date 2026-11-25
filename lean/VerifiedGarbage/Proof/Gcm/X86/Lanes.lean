module

public import VerifiedGarbage.TCB.X86.Sse
public import VerifiedGarbage.Proof.Gcm.Spread32
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseWord
import VerifiedGarbage.Proof.Gcm.Clmul.Arith
import VerifiedGarbage.Proof.Gcm.X86.Rev
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF

-- separate module: the arithmetic builds beside the symbolic execution, which does not change it

/-!
# GHASH in SSE2's words: the arithmetic

Untrusted: everything here is checked by Lean. What the vector part of
`vg_ghash` on x86 computes, as functions of 128-bit values, and their values
as polynomials over GF(2).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86

open Polynomial VG.X86
open VG.Proof.Gcm.Poly VG.Proof.Gcm.Spread

/-! ## Bits of shifted vectors -/

abbrev psllq (a : BitVec 128) (n : BitVec 8) : BitVec 128 := XShiftOp.eval .psllq a n
abbrev psrlq (a : BitVec 128) (n : BitVec 8) : BitVec 128 := XShiftOp.eval .psrlq a n
abbrev pslldq (a : BitVec 128) (n : BitVec 8) : BitVec 128 := XShiftOp.eval .pslldq a n
abbrev psrldq (a : BitVec 128) (n : BitVec 8) : BitVec 128 := XShiftOp.eval .psrldq a n
abbrev pslld (a : BitVec 128) (n : BitVec 8) : BitVec 128 := XShiftOp.eval .pslld a n
abbrev psrld (a : BitVec 128) (n : BitVec 8) : BitVec 128 := XShiftOp.eval .psrld a n
abbrev psraw (a : BitVec 128) (n : BitVec 8) : BitVec 128 := XShiftOp.eval .psraw a n
abbrev paddw (a b : BitVec 128) : BitVec 128 := XBinOp.eval .paddw a b
abbrev pxor (a b : BitVec 128) : BitVec 128 := XBinOp.eval .pxor a b
abbrev pand (a b : BitVec 128) : BitVec 128 := XBinOp.eval .pand a b
abbrev por (a b : BitVec 128) : BitVec 128 := XBinOp.eval .por a b
abbrev lwd (a b : BitVec 128) : BitVec 128 := XBinOp.eval .punpcklwd a b
abbrev hwd (a b : BitVec 128) : BitVec 128 := XBinOp.eval .punpckhwd a b
abbrev lqdq (a b : BitVec 128) : BitVec 128 := XBinOp.eval .punpcklqdq a b

theorem pxor_eq (a b : BitVec 128) : pxor a b = a ^^^ b := rfl
theorem pand_eq (a b : BitVec 128) : pand a b = a &&& b := rfl
theorem por_eq (a b : BitVec 128) : por a b = a ||| b := rfl

theorem getLsbD_qword (a : BitVec 128) (j p : Nat) : (qword a j).getLsbD p = (decide (p < 64) && a.getLsbD (64 * j + p)) := by
  rw [qword, BitVec.getLsbD_extractLsb']

theorem qword_append (a b : BitVec 64) : qword (a ++ b) 0 = b ∧ qword (a ++ b) 1 = a := by
  refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;> rw [getLsbD_qword, BitVec.getLsbD_append]
  · simp [hi]
  · simp [hi]

theorem append_qword (a : BitVec 128) : qword a 1 ++ qword a 0 = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append, getLsbD_qword, getLsbD_qword]
  by_cases h : i < 64
  · simp [h]
  · simp [h, show i - 64 < 64 by omega, show 64 + (i - 64) = i by omega]

theorem qword_psllq (a : BitVec 128) {n : BitVec 8} (hn : n.toNat < 64) (j : Nat) (hj : j < 2) :
    qword (psllq a n) j = qword a j <<< n.toNat := by
  rw [show psllq a n = if 63 < n.toNat then 0 else (qword a 1 <<< n.toNat) ++ (qword a 0 <<< n.toNat) from rfl,
    ite_eq_right (by omega)]
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · exact (qword_append _ _).1
  · exact (qword_append _ _).2

theorem qword_psrlq (a : BitVec 128) {n : BitVec 8} (hn : n.toNat < 64) (j : Nat) (hj : j < 2) :
    qword (psrlq a n) j = qword a j >>> n.toNat := by
  rw [show psrlq a n = if 63 < n.toNat then 0 else (qword a 1 >>> n.toNat) ++ (qword a 0 >>> n.toNat) from rfl,
    ite_eq_right (by omega)]
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · exact (qword_append _ _).1
  · exact (qword_append _ _).2

theorem qword_pxor (a b : BitVec 128) (j : Nat) : qword (pxor a b) j = qword a j ^^^ qword b j := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_qword, BitVec.getLsbD_xor, pxor_eq, hi, decide_true, Bool.true_and]

/-! ## Eight steps: a product of bytes in a word -/

def st16 (k : BitVec 16) : Nat → BitVec 16 → BitVec 16 × BitVec 16
  | 0, y => (y, y.sshiftRight 15 &&& k)
  | n + 1, y =>
    let p := st16 k n y
    (p.1 + p.1, (p.2 + p.2) ^^^ ((p.1 + p.1).sshiftRight 15 &&& k))

def st128 (k : BitVec 128) : Nat → BitVec 128 → BitVec 128 × BitVec 128
  | 0, y => (y, pand (psraw y 15) k)
  | n + 1, y =>
    let p := st128 k n y
    (paddw p.1 p.1, pxor (paddw p.2 p.2) (pand (psraw (paddw p.1 p.1) 15) k))

theorem word_psraw15 (a : BitVec 128) {i : Nat} (hi : i < 8) : word (psraw a 15) i = (word a i).sshiftRight 15 :=
  word_psraw a 15 hi

theorem word_st128 (k y : BitVec 128) {i : Nat} (hi : i < 8) (n : Nat) :
    word (st128 k n y).1 i = (st16 (word k i) n (word y i)).1 ∧
      word (st128 k n y).2 i = (st16 (word k i) n (word y i)).2 := by
  induction n with
  | zero => exact ⟨rfl, by rw [st128, word_pand, word_psraw15 _ hi]; rfl⟩
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · rw [st128, word_paddw _ _ hi, ih.1]; rfl
    · rw [st128, word_pxor, word_paddw _ _ hi, word_pand, word_psraw15 _ hi, word_paddw _ _ hi, ih.1, ih.2]; rfl

theorem add_self16 (v : BitVec 16) : v + v = v <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem st16_fst (k y : BitVec 16) (n : Nat) : (st16 k n y).1 = y <<< n := by
  induction n with
  | zero => exact (BitVec.shiftLeft_zero y).symm
  | succ n ih => rw [st16]; show (st16 k n y).1 + (st16 k n y).1 = _; rw [ih, add_self16, ← BitVec.shiftLeft_add]

/-- The mask of a word's top bit. -/
theorem sar15_and (v k : BitVec 16) : v.sshiftRight 15 &&& k = if v.getLsbD 15 then k else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last]
  by_cases h : 15 + i < 16
  · obtain rfl : i = 0 := by omega
    cases hv : v.getLsbD 15 <;> simp []
  · cases hv : v.getLsbD 15 <;> simp [h, hi, show ¬ 16 ≤ i by omega]

theorem lp_shl1 (v : BitVec 16) (h : v.getLsbD 15 = false) : lp (v <<< 1) = X * lp v := by
  ext d
  rw [coeff_lp, BitVec.getLsbD_shiftLeft]
  cases d with
  | zero => simp [bit]
  | succ d =>
    rw [coeff_X_mul, coeff_lp]
    by_cases hd : d + 1 < 16
    · simp [hd]
    · by_cases h15 : d = 15
      · subst h15; rw [h]; rfl
      · simp [hd, BitVec.getLsbD_of_ge v d (by omega)]

theorem lp_step (y : BitVec 16) {n : Nat} (hn : n < 15) :
    lp (y >>> (14 - n)) = X * lp (y >>> (15 - n)) + C (bit (y.getLsbD (14 - n))) := by
  ext d
  rw [coeff_lp, coeff_add, BitVec.getLsbD_ushiftRight]
  cases d with
  | zero => simp
  | succ d =>
    rw [coeff_X_mul, coeff_lp, coeff_C, BitVec.getLsbD_ushiftRight, ite_eq_right (Nat.succ_ne_zero d), add_zero,
      show 14 - n + (d + 1) = 15 - n + d by omega]

theorem lp_ite (b : Bool) (k : BitVec 16) : lp (if b then k else 0) = C (bit b) * lp k := by
  cases b
  · rw [ite_eq_right (by decide), show (0 : BitVec 16) = 0#16 from rfl, lp_zero]; simp [bit]
  · rw [ite_eq_left rfl]; simp [bit]

theorem st16_snd (k y : BitVec 16) (hk : ∀ p, 8 ≤ p → k.getLsbD p = false) {n : Nat} (hn : n < 8) :
    lp (st16 k n y).2 = lp (y >>> (15 - n)) * lp k ∧ ∀ p, 8 + n ≤ p → (st16 k n y).2.getLsbD p = false := by
  induction n with
  | zero =>
    have h15 : lp (y >>> 15) = C (bit (y.getLsbD 15)) := by
      ext d
      rw [coeff_lp, coeff_C, BitVec.getLsbD_ushiftRight]
      by_cases h : d = 0
      · subst h; rw [ite_eq_left rfl]
      · rw [ite_eq_right h, BitVec.getLsbD_of_ge y (15 + d) (by omega)]; simp [bit]
    refine ⟨?_, fun p hp => ?_⟩
    · rw [st16, sar15_and, lp_ite, h15]
    · rw [st16, sar15_and]
      split
      · exact hk p (by omega)
      · simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hb : ((st16 k n y).1 + (st16 k n y).1).sshiftRight 15 &&& k = if y.getLsbD (14 - n) then k else 0 := by
      rw [st16_fst, add_self16, ← BitVec.shiftLeft_add, sar15_and, BitVec.getLsbD_shiftLeft]
      simp only [show ¬ 15 < n + 1 by omega, show 15 - (n + 1) = 14 - n by omega, decide_false, Bool.not_false,
        Nat.lt_add_one, decide_true, Bool.true_and]
    refine ⟨?_, fun p hp => ?_⟩
    · rw [st16]
      show lp (((st16 k n y).2 + (st16 k n y).2) ^^^ _) = _
      rw [hb, lp_xor, add_self16, lp_shl1 _ (h2 15 (by omega)), h1, lp_ite, show 15 - (n + 1) = 14 - n by omega,
        lp_step y (by omega)]
      ring
    · rw [st16]
      show (((st16 k n y).2 + (st16 k n y).2) ^^^ _).getLsbD p = false
      rw [hb, add_self16, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, h2 (p - 1) (by omega), Bool.and_false, Bool.false_xor]
      split
      · exact hk p (by omega)
      · simp

/-! ## A vector of eight products of words -/

/-- The bytes of the words. -/
def c00ff : BitVec 128 := 0x00ff00ff00ff00ff00ff00ff00ff00ff#128

theorem getLsbD_c00ff {p : Nat} (hp : p < 128) : c00ff.getLsbD p = decide (p % 16 < 8) := by
  have : ∀ p < 128, c00ff.getLsbD p = decide (p % 16 < 8) := by decide +kernel
  exact this p hp

theorem getLsbD_psllq (a : BitVec 128) {n : BitVec 8} (hn : n.toNat < 64) {p : Nat} (hp : p < 128) :
    (psllq a n).getLsbD p = (decide (n.toNat ≤ p % 64) && a.getLsbD (p - n.toNat)) := by
  have hq := congrArg (fun q : BitVec 64 => q.getLsbD (p % 64)) (qword_psllq a hn (p / 64) (by omega))
  simp only [getLsbD_qword, BitVec.getLsbD_shiftLeft, show p % 64 < 64 by omega, decide_true, Bool.true_and,
    show 64 * (p / 64) + p % 64 = p by omega] at hq
  rw [hq]
  by_cases h : p % 64 < n.toNat
  · simp [h, show ¬ n.toNat ≤ p % 64 by omega]
  · simp [h, show n.toNat ≤ p % 64 by omega, show p % 64 - n.toNat < 64 by omega,
      show 64 * (p / 64) + (p % 64 - n.toNat) = p - n.toNat by omega]

theorem getLsbD_psrlq (a : BitVec 128) {n : BitVec 8} (hn : n.toNat < 64) {p : Nat} (hp : p < 128) :
    (psrlq a n).getLsbD p = (decide (p % 64 + n.toNat < 64) && a.getLsbD (p + n.toNat)) := by
  have hq := congrArg (fun q : BitVec 64 => q.getLsbD (p % 64)) (qword_psrlq a hn (p / 64) (by omega))
  simp only [getLsbD_qword, BitVec.getLsbD_ushiftRight, show p % 64 < 64 by omega, decide_true, Bool.true_and,
    show 64 * (p / 64) + p % 64 = p by omega] at hq
  rw [hq, show n.toNat + p % 64 = p % 64 + n.toNat by omega, show 64 * (p / 64) + (p % 64 + n.toNat) = p + n.toNat by omega]

structure Pair where
  a : BitVec 128
  b : BitVec 128

/-- The products of the words of `w` and of the words of which `kl` and `kh`
are the bytes, 32 bits each, the first four and the last. -/
def vecs (w kl kh : BitVec 128) : Pair :=
  let s := pxor (psllq w 8) w
  let h := (st128 kh 7 w).2
  let w8 := paddw (st128 kh 7 w).1 (st128 kh 7 w).1
  let l := (st128 kl 7 w8).2
  let m := pxor (pxor (st128 (pxor kh kl) 7 s).2 h) l
  let t := pand m c00ff
  let m' := pxor m t
  let l' := pxor l (psllq t 8)
  let h' := pxor h (psrlq m' 8)
  ⟨lwd l' h', hwd l' h'⟩

/-- A vector of bytes in its words. -/
def Bytes (k : BitVec 128) : Prop := ∀ i < 8, ∀ p, 8 ≤ p → (word k i).getLsbD p = false

/-- What the bytes of a key's words are. -/
structure KeyB (K kl kh : BitVec 128) : Prop where
  l : Bytes kl
  h : Bytes kh
  e : ∀ i < 8, lp (word K i) = lp (word kl i) + X ^ 8 * lp (word kh i)

theorem lp_shift16 (v : BitVec 16) : lp (v <<< 8) + X ^ 16 * lp (v >>> 8) = X ^ 8 * lp v := by
  ext d
  rw [coeff_add, coeff_X_pow_mul', coeff_X_pow_mul', coeff_lp, coeff_lp, coeff_lp, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  by_cases h1 : d < 16
  · by_cases h2 : d < 8
    · simp [h1, h2, show ¬ 16 ≤ d by omega, show ¬ 8 ≤ d by omega, bit]
    · simp [h1, h2, show ¬ 16 ≤ d by omega, show 8 ≤ d by omega]
  · simp [h1, show 16 ≤ d by omega, show 8 ≤ d by omega, show 8 + (d - 16) = d - 8 by omega, bit]

/-- A word from its bytes. -/
theorem lp_bytes (v : BitVec 16) : lp v = lp ((v <<< 8) >>> 8) + X ^ 8 * lp (v >>> 8) := by
  ext d
  rw [coeff_add, coeff_X_pow_mul', coeff_lp, coeff_lp, coeff_lp, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  by_cases h : d < 8
  · simp [show 8 + d < 16 by omega, show ¬ 8 ≤ d by omega]
  · simp [show ¬ 8 + d < 16 by omega, show 8 ≤ d by omega, show 8 + (d - 8) = d by omega, bit]

theorem word_psllq8 (a : BitVec 128) {i : Nat} (hi : i < 8) (p : Nat) (hp : p < 16) (h8 : 8 ≤ p) :
    (word (psllq a 8) i).getLsbD p = (word a i).getLsbD (p - 8) := by
  rw [getLsbD_word _ _ _ hp, getLsbD_word _ _ _ (by omega), getLsbD_psllq a (by decide) (by omega)]
  simp only [show (8 : BitVec 8).toNat = 8 from rfl, show 8 ≤ (16 * i + p) % 64 by omega, decide_true, Bool.true_and]
  exact congrArg _ (by omega)

/-- The bytes of a word moved up, their low ones taken. -/
theorem word_up (m : BitVec 128) {i : Nat} (hi : i < 8) : word (psllq (pand m c00ff) 8) i = word m i <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [BitVec.getLsbD_shiftLeft]
  by_cases h : p < 8
  · rw [getLsbD_word _ _ _ hp, getLsbD_psllq _ (by decide) (by omega)]
    simp only [show (8 : BitVec 8).toNat = 8 from rfl, h, decide_true, Bool.not_true, Bool.false_and, Bool.and_false]
    by_cases h' : 8 ≤ (16 * i + p) % 64
    · rw [pand_eq, BitVec.getLsbD_and, getLsbD_c00ff (by omega),
        decide_eq_false (show ¬ (16 * i + p - 8) % 16 < 8 by omega), Bool.and_false, Bool.and_false]
    · rw [decide_eq_false h', Bool.false_and]
  · rw [word_psllq8 _ hi p hp (by omega), getLsbD_word _ _ _ (by omega), getLsbD_word _ _ _ (by omega), pand_eq,
      BitVec.getLsbD_and, getLsbD_c00ff (by omega), decide_eq_true (show (16 * i + (p - 8)) % 16 < 8 by omega), Bool.and_true]
    simp [hp, h]

theorem word_down (m : BitVec 128) {i : Nat} (hi : i < 8) :
    word (psrlq (pxor m (pand m c00ff)) 8) i = word m i >>> 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [BitVec.getLsbD_ushiftRight, getLsbD_word _ _ _ hp, getLsbD_psrlq _ (by decide) (by omega)]
  simp only [show (8 : BitVec 8).toNat = 8 from rfl]
  by_cases h : p < 8
  · rw [decide_eq_true (show (16 * i + p) % 64 + 8 < 64 by omega), Bool.true_and, pxor_eq, pand_eq, BitVec.getLsbD_xor,
      BitVec.getLsbD_and, getLsbD_c00ff (by omega), decide_eq_false (show ¬ (16 * i + p + 8) % 16 < 8 by omega),
      Bool.and_false, Bool.xor_false, getLsbD_word _ _ _ (by omega)]
    exact congrArg _ (by omega)
  · rw [BitVec.getLsbD_of_ge (word m i) (8 + p) (by omega)]
    by_cases h' : (16 * i + p) % 64 + 8 < 64
    · rw [pxor_eq, pand_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and, getLsbD_c00ff (by omega),
        decide_eq_true (show (16 * i + p + 8) % 16 < 8 by omega), Bool.and_true, Bool.xor_self, Bool.and_false]
    · rw [decide_eq_false h', Bool.false_and]

theorem dword_lwd (a b : BitVec 128) {j : Nat} (hj : j < 4) : dword (lwd a b) j = word b j ++ word a j := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [getLsbD_dword, BitVec.getLsbD_append]
  by_cases h : p < 16
  · have e := congrArg (fun v : BitVec 16 => v.getLsbD p) (word_punpcklwd a b (i := 2 * j) (by omega))
    simp only [getLsbD_word _ _ _ h, show 2 * j % 2 = 0 by omega, ite_true, show 2 * j / 2 = j by omega,
      show 16 * (2 * j) + p = 32 * j + p by omega] at e
    simp only [h, hp, ite_true, decide_true, Bool.true_and, getLsbD_word _ _ _ h]
    exact e
  · have h' : p - 16 < 16 := by omega
    have e := congrArg (fun v : BitVec 16 => v.getLsbD (p - 16)) (word_punpcklwd a b (i := 2 * j + 1) (by omega))
    simp only [getLsbD_word _ _ _ h', show ¬ (2 * j + 1) % 2 = 0 by omega, ite_false, show (2 * j + 1) / 2 = j by omega,
      show 16 * (2 * j + 1) + (p - 16) = 32 * j + p by omega] at e
    simp only [h, hp, ite_false, decide_true, Bool.true_and, getLsbD_word _ _ _ h']
    exact e

theorem dword_hwd (a b : BitVec 128) {j : Nat} (hj : j < 4) : dword (hwd a b) j = word b (4 + j) ++ word a (4 + j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [getLsbD_dword, BitVec.getLsbD_append]
  by_cases h : p < 16
  · have e := congrArg (fun v : BitVec 16 => v.getLsbD p) (word_punpckhwd a b (i := 2 * j) (by omega))
    simp only [getLsbD_word _ _ _ h, show 2 * j % 2 = 0 by omega, ite_true, show 2 * j / 2 = j by omega,
      show 16 * (2 * j) + p = 32 * j + p by omega] at e
    simp only [h, hp, ite_true, decide_true, Bool.true_and, getLsbD_word _ _ _ h]
    exact e
  · have h' : p - 16 < 16 := by omega
    have e := congrArg (fun v : BitVec 16 => v.getLsbD (p - 16)) (word_punpckhwd a b (i := 2 * j + 1) (by omega))
    simp only [getLsbD_word _ _ _ h', show ¬ (2 * j + 1) % 2 = 0 by omega, ite_false, show (2 * j + 1) / 2 = j by omega,
      show 16 * (2 * j + 1) + (p - 16) = 32 * j + p by omega] at e
    simp only [h, hp, ite_false, decide_true, Bool.true_and, getLsbD_word _ _ _ h']
    exact e

/-- A lane of the last steps. -/
theorem lane_ok {H L M : BitVec 128} {i : Nat} (hi : i < 8) {wl wh kl kh : P} (eh : lp (word H i) = wh * kh)
    (el : lp (word L i) = wl * kl) (em : lp (word M i) = (wl + wh) * (kh + kl)) :
    lp (word (pxor H (psrlq (pxor (pxor (pxor M H) L) (pand (pxor (pxor M H) L) c00ff)) 8)) i ++
      word (pxor L (psllq (pand (pxor (pxor M H) L) c00ff) 8)) i) = (wl + X ^ 8 * wh) * (kl + X ^ 8 * kh) := by
  have h2 : (2 : P) = 0 := CharTwo.two_eq_zero
  have hm : lp (word (pxor (pxor M H) L) i) = (wl + wh) * (kh + kl) + wh * kh + wl * kl := by
    rw [word_pxor, word_pxor, lp_xor, lp_xor, em, eh, el]
  generalize pxor (pxor M H) L = m at hm ⊢
  have hs := lp_shift16 (word m i)
  rw [hm] at hs
  rw [lp_append, word_pxor, word_pxor, word_up _ hi, word_down _ hi, lp_xor, lp_xor, eh, el]
  linear_combination hs + X ^ 8 * (wh * kh + wl * kl) * h2

theorem vecs_lane {w K kl kh : BitVec 128} (hK : KeyB K kl kh) {i : Nat} (hi : i < 8) :
    ∃ l' h', vecs w kl kh = ⟨lwd l' h', hwd l' h'⟩ ∧ lp (word h' i ++ word l' i) = lp (word w i) * lp (word K i) := by
  have kl8 := hK.l i hi
  have kh8 := hK.h i hi
  have ks8 : ∀ p, 8 ≤ p → (word (pxor kh kl) i).getLsbD p = false := fun p hp => by
    rw [word_pxor, BitVec.getLsbD_xor, kl8 p hp, kh8 p hp]; rfl
  have w8 : word (paddw (st128 kh 7 w).1 (st128 kh 7 w).1) i = word w i <<< 8 := by
    rw [word_paddw _ _ hi, (word_st128 kh w hi 7).1, st16_fst, add_self16, ← BitVec.shiftLeft_add]
  have es : word (pxor (psllq w 8) w) i >>> 8 = ((word w i <<< 8) >>> 8) ^^^ (word w i >>> 8) := by
    apply BitVec.eq_of_getLsbD_eq
    intro p hp
    rw [word_pxor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    by_cases h : p < 8
    · rw [word_psllq8 _ hi _ (by omega) (by omega)]
      simp [show 8 + p < 16 by omega]
    · rw [BitVec.getLsbD_of_ge (word (psllq w 8) i) (8 + p) (by omega)]
      simp [show ¬ 8 + p < 16 by omega]
  refine ⟨_, _, rfl, ?_⟩
  rw [hK.e i hi, lp_bytes (word w i)]
  refine lane_ok hi ?_ ?_ ?_
  · rw [(word_st128 kh w hi 7).2, (st16_snd _ _ kh8 (by decide)).1]
  · rw [(word_st128 kl _ hi 7).2, (st16_snd _ _ kl8 (by decide)).1, w8]
  · rw [(word_st128 _ _ hi 7).2, (st16_snd _ _ ks8 (by decide)).1, es, lp_xor, word_pxor, lp_xor]

theorem vecs_ok {w K kl kh : BitVec 128} (hK : KeyB K kl kh) :
    (∀ j < 4, lp (dword (vecs w kl kh).a j) = lp (word w j) * lp (word K j)) ∧
      ∀ j < 4, lp (dword (vecs w kl kh).b j) = lp (word w (4 + j)) * lp (word K (4 + j)) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · obtain ⟨l', h', e, v⟩ := vecs_lane (w := w) hK (show j < 8 by omega)
    rw [e, ← v]; exact congrArg _ (dword_lwd _ _ hj)
  · obtain ⟨l', h', e, v⟩ := vecs_lane (w := w) hK (show 4 + j < 8 by omega)
    rw [e, ← v]; exact congrArg _ (dword_hwd _ _ hj)

/-! ## The key's bytes -/

def kbl (K : BitVec 128) : BitVec 128 := pand K c00ff
def kbh (K : BitVec 128) : BitVec 128 := psrlq (pxor K (pand K c00ff)) 8

theorem word_kbl (K : BitVec 128) {i : Nat} (hi : i < 8) : word (kbl K) i = (word K i <<< 8) >>> 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [getLsbD_word _ _ _ hp, kbl, pand_eq, BitVec.getLsbD_and, getLsbD_c00ff (by omega), BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, show (16 * i + p) % 16 = p by omega]
  by_cases h : p < 8
  · simp [h, show 8 + p < 16 by omega, getLsbD_word _ _ _ hp]
  · simp [h, show ¬ 8 + p < 16 by omega]

theorem keyB (K : BitVec 128) : KeyB K (kbl K) (kbh K) := by
  refine ⟨fun i hi p hp => ?_, fun i hi p hp => ?_, fun i hi => ?_⟩
  · rw [word_kbl K hi, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, decide_eq_false (show ¬ 8 + p < 16 by omega)]
    rfl
  · rw [kbh, word_down K hi, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_of_ge _ _ (by omega)]
  · rw [word_kbl K hi, kbh, word_down K hi, ← lp_bytes]

/-! ## Doublewords and quadwords -/

theorem lp_dword (v : BitVec 128) (j : Nat) :
    lp (dword v j) = lp (word v (2 * j)) + X ^ 16 * lp (word v (2 * j + 1)) := by
  ext d
  rw [coeff_add, coeff_X_pow_mul', coeff_lp, coeff_lp, coeff_lp, getLsbD_dword]
  by_cases h : d < 16
  · rw [ite_eq_right (by omega), add_zero, getLsbD_word _ _ _ h]
    simp [show d < 32 by omega, show 16 * (2 * j) + d = 32 * j + d by omega]
  · rw [BitVec.getLsbD_of_ge _ d (by omega), ite_eq_left (by omega)]
    by_cases h' : d - 16 < 16
    · rw [getLsbD_word _ _ _ h']
      simp [show d < 32 by omega, show 16 * (2 * j + 1) + (d - 16) = 32 * j + d by omega, bit]
    · rw [BitVec.getLsbD_of_ge _ (d - 16) (by omega)]
      simp [show ¬ d < 32 by omega, bit]

theorem lp_qword (v : BitVec 128) (j : Nat) :
    lp (qword v j) = lp (dword v (2 * j)) + X ^ 32 * lp (dword v (2 * j + 1)) := by
  ext d
  rw [coeff_add, coeff_X_pow_mul', coeff_lp, coeff_lp, coeff_lp, getLsbD_dword, getLsbD_dword, getLsbD_qword]
  by_cases h : d < 32
  · simp [h, show d < 64 by omega, show ¬ 32 ≤ d by omega, show 32 * (2 * j) + d = 64 * j + d by omega]
  · by_cases h' : d < 64
    · simp [h, h', show 32 ≤ d by omega, show d - 32 < 32 by omega,
        show 32 * (2 * j + 1) + (d - 32) = 64 * j + d by omega, bit]
    · simp [h, h', show ¬ d - 32 < 32 by omega, bit]

theorem lp_vec (v : BitVec 128) : lp v = lp (qword v 0) + X ^ 64 * lp (qword v 1) := by
  conv_lhs => rw [← append_qword v]
  exact lp_append _ _

theorem dword_xor (a b : BitVec 128) (j : Nat) : dword (pxor a b) j = dword a j ^^^ dword b j := dword_pxor a b j

theorem dword_psrlq32 (q : BitVec 128) {j : Nat} (hj : j < 2) : dword (psrlq q 32) (2 * j) = dword q (2 * j + 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [getLsbD_dword, getLsbD_dword, getLsbD_psrlq _ (by decide) (by omega)]
  simp only [show (32 : BitVec 8).toNat = 32 from rfl, hp, decide_true, Bool.true_and,
    show (32 * (2 * j) + p) % 64 + 32 < 64 by omega]
  exact congrArg _ (by omega)

/-- The middle products added to quadwords of a doubleword's two. -/
def fix (q s : BitVec 128) : BitVec 128 := pxor q (psrlq (psllq (pxor (pxor (psrlq q 32) q) s) 32) 16)

theorem lp_mid (v : BitVec 64) : lp ((v <<< 32) >>> 16) = X ^ 16 * lp (v.extractLsb' 0 32) := by
  ext d
  rw [coeff_lp, coeff_X_pow_mul', coeff_lp, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb']
  by_cases h : 16 ≤ d
  · by_cases h' : d < 48
    · simp [h, show 16 + d < 64 by omega, show ¬ 16 + d < 32 by omega, show d - 16 < 32 by omega,
        show 16 + d - 32 = d - 16 by omega]
    · simp [show ¬ 16 + d < 64 by omega, show ¬ d - 16 < 32 by omega, bit]
  · simp [h, show 16 + d < 32 by omega, bit]

theorem extract_qword (v : BitVec 128) (j : Nat) : (qword v j).extractLsb' 0 32 = dword v (2 * j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [BitVec.getLsbD_extractLsb', getLsbD_qword, getLsbD_dword, Nat.zero_add]
  simp [hp, show p < 64 by omega, show 64 * j + p = 32 * (2 * j) + p by omega]

/-- A doubleword's product of its words' three. -/
theorem fix_ok {q s : BitVec 128} {j : Nat} (hj : j < 2) {w0 w1 k0 k1 : P} (h0 : lp (dword q (2 * j)) = w0 * k0)
    (h1 : lp (dword q (2 * j + 1)) = w1 * k1) (hs : lp (dword s (2 * j)) = (w0 + w1) * (k0 + k1)) :
    lp (qword (fix q s) j) = (w0 + X ^ 16 * w1) * (k0 + X ^ 16 * k1) := by
  have h2 : (2 : P) = 0 := CharTwo.two_eq_zero
  rw [fix, qword_pxor, lp_xor, qword_psrlq _ (by decide) j hj, qword_psllq _ (by decide) j hj]
  simp only [show (32 : BitVec 8).toNat = 32 from rfl, show (16 : BitVec 8).toNat = 16 from rfl]
  rw [lp_mid, extract_qword, dword_xor, dword_xor, dword_psrlq32 _ hj, lp_xor, lp_xor, h0, h1, hs, lp_qword, h0, h1]
  linear_combination X ^ 16 * (w0 * k0 + w1 * k1) * h2

/-! ## The words multiplied -/

def u1F (y : BitVec 128) : BitVec 128 := pxor (shufDwords y 0x84) (shufDwords y 0xde)
def u2F (y u : BitVec 128) : BitVec 128 :=
  por (psrld (pxor (pslld y 16) y) 16) (pslld (psrld (pxor (pslld u 16) u) 16) 16)

theorem dword_u1 (y : BitVec 128) : dword (u1F y) 0 = dword y 0 ^^^ dword y 2 ∧ dword (u1F y) 1 = dword y 1 ^^^ dword y 3 ∧
    dword (u1F y) 2 = dword y 0 ^^^ dword y 1 ∧ dword (u1F y) 3 = dword y 2 ^^^ dword y 3 := by
  simp only [u1F, dword_xor, shufDwords, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem word_u2 (y u : BitVec 128) {j : Nat} (hj : j < 4) :
    word (u2F y u) (2 * j) = word y (2 * j) ^^^ word y (2 * j + 1) ∧
      word (u2F y u) (2 * j + 1) = word u (2 * j) ^^^ word u (2 * j + 1) := by
  have e : dword (u2F y u) j = ((dword y j <<< 16 ^^^ dword y j) >>> 16) |||
      (((dword u j <<< 16 ^^^ dword u j) >>> 16) <<< 16) := by
    rw [u2F]
    show dword (XBinOp.eval .por _ _) j = _
    rw [dword_por, dword_psrld _ _ (by decide) hj, dword_pslld _ _ (by decide) hj, dword_psrld _ _ (by decide) hj,
      dword_xor, dword_xor, dword_pslld _ _ (by decide) hj, dword_pslld _ _ (by decide) hj]
    rfl
  have w0 : ∀ v : BitVec 128, word v (2 * j) = (dword v j).extractLsb' 0 16 := fun v => word_dword v j 0 (by decide)
  have w1 : ∀ v : BitVec 128, word v (2 * j + 1) = (dword v j).extractLsb' 16 16 := fun v => word_dword v j 1 (by decide)
  rw [w0, w1, w0, w1, w0, w1, e]
  generalize dword y j = a
  generalize dword u j = b
  refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro p hp <;>
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_xor, hp, decide_true, Bool.true_and]
  · simp [show 16 + p < 32 by omega, show p < 16 by omega, Bool.xor_comm]
  · simp [BitVec.getLsbD_of_ge a (16 + (16 + p)) (by omega), show ¬ 16 + (16 + p) < 32 by omega,
      show 16 + p < 32 by omega, show 16 + p - 16 = p by omega]

/-! ## Karatsuba's sums -/

theorem lp_pslldq8 (v : BitVec 128) : lp (pslldq v 8) = X ^ 64 * lp (qword v 0) := by
  ext d
  rw [show pslldq v 8 = v <<< 64 from rfl, coeff_lp, coeff_X_pow_mul', coeff_lp, BitVec.getLsbD_shiftLeft, getLsbD_qword]
  by_cases h : d < 128
  · by_cases h' : 64 ≤ d
    · simp [h, h', show ¬ d < 64 by omega, show d - 64 < 64 by omega]
    · simp [h', show d < 64 by omega, bit]
  · simp [h, show ¬ d - 64 < 64 by omega, bit]

theorem lp_psrldq8 (v : BitVec 128) : lp (psrldq v 8) = lp (qword v 1) := by
  ext d
  rw [show psrldq v 8 = v >>> 64 from rfl, coeff_lp, coeff_lp, BitVec.getLsbD_ushiftRight, getLsbD_qword]
  by_cases h : d < 64
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge v (64 + d) (by omega)]

theorem lp_midlo (v : BitVec 128) : lp (psrldq (pslldq v 8) 4) = X ^ 32 * lp (qword v 0) := by
  ext d
  rw [show psrldq (pslldq v 8) 4 = (v <<< 64) >>> 32 from rfl, coeff_lp, coeff_X_pow_mul', coeff_lp,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, getLsbD_qword]
  by_cases h : 32 ≤ d
  · by_cases h' : d < 96
    · simp [h, show 32 + d < 128 by omega, show ¬ 32 + d < 64 by omega, show d - 32 < 64 by omega,
        show 32 + d - 64 = d - 32 by omega]
    · simp [show ¬ 32 + d < 128 by omega, show ¬ d - 32 < 64 by omega, bit]
  · simp [h, show 32 + d < 64 by omega, bit]

theorem lp_midhi (v : BitVec 128) : lp (pslldq (psrldq v 8) 4) = X ^ 32 * lp (qword v 1) := by
  ext d
  rw [show pslldq (psrldq v 8) 4 = (v >>> 64) <<< 32 from rfl, coeff_lp, coeff_X_pow_mul', coeff_lp,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, getLsbD_qword]
  by_cases h : 32 ≤ d
  · by_cases h' : d < 96
    · simp [h, show d < 128 by omega, show ¬ d < 32 by omega, show d - 32 < 64 by omega]
    · simp [show ¬ d - 32 < 64 by omega, BitVec.getLsbD_of_ge v (64 + (d - 32)) (by omega), bit]
  · simp [h, show d < 32 by omega, bit]

theorem qword_swap (v : BitVec 128) : qword (shufDwords v 0x4e) 0 = qword v 1 ∧ qword (shufDwords v 0x4e) 1 = qword v 0 := by
  have e0 : ∀ j, j < 2 → ∀ p < 64, (qword (shufDwords v 0x4e) j).getLsbD p =
      if p < 32 then (dword (shufDwords v 0x4e) (2 * j)).getLsbD p else
        (dword (shufDwords v 0x4e) (2 * j + 1)).getLsbD (p - 32) := by
    intro j hj p hp
    by_cases h : p < 32
    · rw [ite_eq_left h, getLsbD_qword, getLsbD_dword]; simp [h, hp, show 64 * j + p = 32 * (2 * j) + p by omega]
    · rw [ite_eq_right h, getLsbD_qword, getLsbD_dword]
      simp [hp, show p - 32 < 32 by omega, show 32 * (2 * j + 1) + (p - 32) = 64 * j + p by omega]
  have d0 : dword (shufDwords v 0x4e) 0 = dword v 2 := dword_ofDwords_0 ..
  have d1 : dword (shufDwords v 0x4e) 1 = dword v 3 := dword_ofDwords_1 ..
  have d2 : dword (shufDwords v 0x4e) 2 = dword v 0 := dword_ofDwords_2 ..
  have d3 : dword (shufDwords v 0x4e) 3 = dword v 1 := dword_ofDwords_3 ..
  refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro p hp
  · rw [e0 0 (by decide) p hp]
    simp only [Nat.mul_zero, Nat.zero_add, d0, d1]
    by_cases h : p < 32
    · rw [ite_eq_left h, getLsbD_qword, getLsbD_dword]; simp [h, hp]
    · rw [ite_eq_right h, getLsbD_qword, getLsbD_dword]
      simp [hp, show p - 32 < 32 by omega, show 96 + (p - 32) = 64 + p by omega]
  · rw [e0 1 (by decide) p hp]
    simp only [Nat.mul_one, Nat.reduceAdd, d2, d3]
    by_cases h : p < 32
    · rw [ite_eq_left h, getLsbD_qword, getLsbD_dword]; simp [h, hp]
    · rw [ite_eq_right h, getLsbD_qword, getLsbD_dword]
      simp [hp, show p - 32 < 32 by omega, show 32 + (p - 32) = p by omega]

theorem qword_lqdq (a b : BitVec 128) : qword (lqdq a b) 0 = qword a 0 ∧ qword (lqdq a b) 1 = qword b 0 :=
  qword_append (qword b 0) (qword a 0)

/-- The low and high halves of a product of two blocks, of nine products of
doublewords. -/
def asm (x y z w v : BitVec 128) : Pair :=
  let t := pxor w (lqdq (pxor (shufDwords x 0x4e) x) (pxor (shufDwords y 0x4e) y))
  let u := pxor t z
  let m := pxor (pxor (pxor (psrldq (pslldq (pxor (pxor (shufDwords u 0x4e) u) v) 8) 4) z) x) y
  ⟨pxor (pxor x (psrldq (pslldq t 8) 4)) (pslldq m 8), pxor (pxor y (pslldq (psrldq t 8) 4)) (psrldq m 8)⟩

theorem asm_ok {x y z w v : BitVec 128} {d0 d1 d2 d3 k0 k1 k2 k3 : P} (x0 : lp (qword x 0) = d0 * k0)
    (x1 : lp (qword x 1) = d1 * k1) (y0 : lp (qword y 0) = d2 * k2) (y1 : lp (qword y 1) = d3 * k3)
    (z0 : lp (qword z 0) = (d0 + d2) * (k0 + k2)) (z1 : lp (qword z 1) = (d1 + d3) * (k1 + k3))
    (w0 : lp (qword w 0) = (d0 + d1) * (k0 + k1)) (w1 : lp (qword w 1) = (d2 + d3) * (k2 + k3))
    (v0 : lp (qword v 0) = (d0 + d2 + d1 + d3) * (k0 + k2 + k1 + k3)) :
    lp (asm x y z w v).a + X ^ 128 * lp (asm x y z w v).b =
      (d0 + X ^ 32 * d1 + X ^ 64 * (d2 + X ^ 32 * d3)) * (k0 + X ^ 32 * k1 + X ^ 64 * (k2 + X ^ 32 * k3)) := by
  have h2 : (2 : P) = 0 := CharTwo.two_eq_zero
  simp only [asm]
  generalize ht : pxor w (lqdq (pxor (shufDwords x 0x4e) x) (pxor (shufDwords y 0x4e) y)) = t
  have t0 : lp (qword t 0) = (d0 + d1) * (k0 + k1) + d1 * k1 + d0 * k0 := by
    rw [← ht, qword_pxor, (qword_lqdq _ _).1, qword_pxor, (qword_swap x).1, lp_xor, lp_xor, w0, x1, x0, add_assoc]
  have t1 : lp (qword t 1) = (d2 + d3) * (k2 + k3) + d3 * k3 + d2 * k2 := by
    rw [← ht, qword_pxor, (qword_lqdq _ _).2, qword_pxor, (qword_swap y).1, lp_xor, lp_xor, w1, y1, y0, add_assoc]
  generalize hm : pxor (pxor (pxor (psrldq (pslldq (pxor (pxor (shufDwords (pxor t z) 0x4e) (pxor t z)) v) 8) 4) z) x) y = m
  have em : lp m = X ^ 32 * (lp (qword t 1) + lp (qword z 1) + (lp (qword t 0) + lp (qword z 0)) + lp (qword v 0)) +
      lp z + lp x + lp y := by
    rw [← hm, pxor_eq, pxor_eq, pxor_eq, lp_xor, lp_xor, lp_xor, lp_midlo, qword_pxor, qword_pxor, (qword_swap _).1,
      qword_pxor, qword_pxor, lp_xor, lp_xor, lp_xor, lp_xor]
  have emv := lp_vec m
  rw [em, lp_vec z, lp_vec x, lp_vec y, t0, t1, z0, z1, x0, x1, y0, y1, v0] at emv
  show lp (pxor _ _) + X ^ 128 * lp (pxor _ _) = _
  rw [pxor_eq, pxor_eq, pxor_eq, pxor_eq, lp_xor, lp_xor, lp_xor, lp_xor, lp_midlo, lp_midhi, lp_pslldq8, lp_psrldq8, t0, t1,
    lp_vec x, lp_vec y, x0, x1, y0, y1]
  linear_combination (-X ^ 64) * emv +
    (d0 * k0 * X ^ 32 + d0 * k0 * X ^ 64 + d0 * k0 * X ^ 96 * 2 + d0 * X ^ 96 * k1 + d0 * X ^ 96 * k2 + k0 * X ^ 96 * d1 +
      k0 * X ^ 96 * d2 + X ^ 32 * d1 * k1 + X ^ 64 * d2 * k2 + X ^ 96 * d1 * k1 * 2 + X ^ 96 * d1 * k3 + X ^ 96 * k1 * d3 +
      X ^ 96 * d2 * k2 * 2 + X ^ 96 * d2 * k3 + X ^ 96 * k2 * d3 + X ^ 96 * d3 * k3 * 2 + X ^ 128 * d1 * k1 +
      X ^ 128 * d3 * k3 + X ^ 160 * d2 * k2 + X ^ 160 * d3 * k3) * h2

/-! ## The reduction -/

def dnV (a : BitVec 128) : BitVec 128 :=
  pxor (pxor (psllq a 57) (psllq (psllq a 57) 5)) (psllq (psllq (psllq a 57) 5) 1)

/-- The two halves of a product, reduced. -/
def redV (p : Pair) : BitVec 128 :=
  let r := pxor p.a (pslldq (dnV p.a) 8)
  pxor (pxor (pxor (pxor (pxor p.b (psrldq (dnV r) 8)) r) (psrlq r 1)) (psrlq (psrlq r 1) 1)) (psrlq (psrlq (psrlq r 1) 1) 5)

theorem dn_comm (a b c : BitVec 64) : a ^^^ b ^^^ c = c ^^^ b ^^^ a := by ac_rfl

theorem qword_dnV (a : BitVec 128) {j : Nat} (hj : j < 2) : qword (dnV a) j = dn (qword a j) := by
  have e1 : qword (psllq a 57) j = qword a j <<< 57 := qword_psllq a (by decide) j hj
  have e2 : qword (psllq (psllq a 57) 5) j = qword a j <<< 62 := by
    rw [qword_psllq _ (by decide) j hj, e1]; exact (BitVec.shiftLeft_add _ 57 5).symm
  have e3 : qword (psllq (psllq (psllq a 57) 5) 1) j = qword a j <<< 63 := by
    rw [qword_psllq _ (by decide) j hj, e2]; exact (BitVec.shiftLeft_add _ 62 1).symm
  rw [dnV, qword_pxor, qword_pxor, e1, e2, e3, dn, dn_comm]

theorem qword_pslldq8 (v : BitVec 128) : qword (pslldq v 8) 0 = 0#64 ∧ qword (pslldq v 8) 1 = qword v 0 := by
  rw [show pslldq v 8 = v <<< 64 from rfl]
  refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro p hp <;>
    simp only [getLsbD_qword, BitVec.getLsbD_shiftLeft, hp, decide_true, Bool.true_and]
  · simp [hp]
  · simp [show 64 + p < 128 by omega]

theorem qword_psrldq8 (v : BitVec 128) : qword (psrldq v 8) 0 = qword v 1 ∧ qword (psrldq v 8) 1 = 0#64 := by
  rw [show psrldq v 8 = v >>> 64 from rfl]
  refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro p hp <;>
    simp only [getLsbD_qword, BitVec.getLsbD_ushiftRight, hp, decide_true, Bool.true_and]
  · simp
  · rw [BitVec.getLsbD_of_ge v (64 + (64 * 1 + p)) (by omega)]; simp

theorem xor_up (a r : BitVec 64) : a ^^^ r >>> 1 ^^^ r >>> 2 ^^^ r >>> 7 = a ^^^ up r := by
  rw [up, BitVec.xor_assoc, BitVec.xor_assoc, BitVec.xor_assoc]

theorem redV_words (p : Pair) : qword (redV p) 0 = qword p.b 0 ^^^ dn (qword p.a 1 ^^^ dn (qword p.a 0)) ^^^ qword p.a 0 ^^^
      up (qword p.a 0) ∧
    qword (redV p) 1 = qword p.b 1 ^^^ (qword p.a 1 ^^^ dn (qword p.a 0)) ^^^ up (qword p.a 1 ^^^ dn (qword p.a 0)) := by
  have r0 : qword (pxor p.a (pslldq (dnV p.a) 8)) 0 = qword p.a 0 := by
    rw [qword_pxor, (qword_pslldq8 _).1, BitVec.xor_zero]
  have r1 : qword (pxor p.a (pslldq (dnV p.a) 8)) 1 = qword p.a 1 ^^^ dn (qword p.a 0) := by
    rw [qword_pxor, (qword_pslldq8 _).2, qword_dnV _ (by decide)]
  simp only [redV]
  generalize pxor p.a (pslldq (dnV p.a) 8) = r at r0 r1 ⊢
  have hs : ∀ j < 2, qword (psrlq (psrlq r 1) 1) j = qword r j >>> 2 ∧
      qword (psrlq (psrlq (psrlq r 1) 1) 5) j = qword r j >>> 7 ∧ qword (psrlq r 1) j = qword r j >>> 1 := by
    intro j hj
    have e1 : qword (psrlq r 1) j = qword r j >>> 1 := qword_psrlq r (by decide) j hj
    have e2 : qword (psrlq (psrlq r 1) 1) j = qword r j >>> 2 := by
      rw [qword_psrlq _ (by decide) j hj, e1]; exact (BitVec.shiftRight_add _ 1 1).symm
    refine ⟨e2, ?_, e1⟩
    rw [qword_psrlq _ (by decide) j hj, e2]; exact (BitVec.shiftRight_add _ 2 5).symm
  refine ⟨?_, ?_⟩
  · rw [qword_pxor, qword_pxor, qword_pxor, qword_pxor, qword_pxor, (hs 0 (by decide)).1, (hs 0 (by decide)).2.1,
      (hs 0 (by decide)).2.2, (qword_psrldq8 _).1, qword_dnV _ (by decide), xor_up, r0, r1]
  · rw [qword_pxor, qword_pxor, qword_pxor, qword_pxor, qword_pxor, (hs 1 (by decide)).1, (hs 1 (by decide)).2.1,
      (hs 1 (by decide)).2.2, (qword_psrldq8 _).2, xor_up, r1, BitVec.xor_zero]

theorem lp_pair {a b c d : BitVec 128} (h : lp a + X ^ 128 * lp b = lp c + X ^ 128 * lp d) : a = c ∧ b = d := by
  have hc : ∀ n, (lp a + X ^ 128 * lp b).coeff n = (lp c + X ^ 128 * lp d).coeff n := fun n => by rw [h]
  simp only [coeff_add, coeff_X_pow_mul', coeff_lp] at hc
  refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · have := hc i
    rw [ite_eq_right (by omega), ite_eq_right (by omega), add_zero, add_zero] at this
    exact bit_inj this
  · have := hc (128 + i)
    rw [ite_eq_left (by omega), ite_eq_left (by omega), BitVec.getLsbD_of_ge a _ (by omega),
      BitVec.getLsbD_of_ge c _ (by omega), show 128 + i - 128 = i by omega] at this
    exact bit_inj (add_left_cancel this)

theorem red_shuffle (h1 m0 u l2 x : BitVec 64) : h1 ^^^ m0 ^^^ x ^^^ l2 ^^^ u = h1 ^^^ m0 ^^^ l2 ^^^ u ^^^ x := by ac_rfl

theorem redV_ok {p : Pair} {y1 y0 h1 h0 : BitVec 64} (hp : lp p.a + X ^ 128 * lp p.b =
      (lp y0 + X ^ 64 * lp y1) * (lp (keyW0 h1 h0) + X ^ 64 * lp (keyW1 h1 h0))) :
    redV p = Spec.Gcm.mul (y1 ++ y0 : BitVec 128) (h1 ++ h0 : BitVec 128) := by
  rw [← mul_words]
  generalize keyW0 h1 h0 = k0 at hp ⊢
  generalize keyW1 h1 h0 = k1 at hp ⊢
  have h2 : (2 : P) = 0 := CharTwo.two_eq_zero
  let l := VectorCrypto.polyMul y0 k0
  let h := VectorCrypto.polyMul y1 k1
  let c := VectorCrypto.polyMul (y0 ^^^ y1) (k0 ^^^ k1)
  let m := c ^^^ l ^^^ h
  have hv : ∀ v : BitVec 128, qword v 0 = Clmul.vdword v 0 ∧ qword v 1 = Clmul.vdword v 1 := fun v => ⟨rfl, rfl⟩
  have hl : ∀ v : BitVec 128, lp v = lp (Clmul.vdword v 0) + X ^ 64 * lp (Clmul.vdword v 1) := lp_vec
  have hpair : lp p.a + X ^ 128 * lp p.b =
      lp ((Clmul.vdword l 1 ^^^ Clmul.vdword m 0) ++ Clmul.vdword l 0 : BitVec 128) +
        X ^ 128 * lp (Clmul.vdword h 1 ++ (Clmul.vdword h 0 ^^^ Clmul.vdword m 1) : BitVec 128) := by
    have el : lp l = lp y0 * lp k0 := lp_polyMul y0 k0
    have eh : lp h = lp y1 * lp k1 := lp_polyMul y1 k1
    have em : lp m = lp y0 * lp k1 + lp y1 * lp k0 := by
      show lp (c ^^^ l ^^^ h) = _
      rw [lp_xor, lp_xor, el, eh, show lp c = _ from lp_polyMul _ _, lp_xor, lp_xor]
      linear_combination (lp y0 * lp k0 + lp y1 * lp k1) * h2
    rw [hp, lp_append (n := 64) (m := 64), lp_append (n := 64) (m := 64), lp_xor, lp_xor]
    have e1 := hl l
    have e2 := hl m
    have e3 := hl h
    rw [el] at e1
    rw [em] at e2
    rw [eh] at e3
    linear_combination e1 + X ^ 64 * e2 + X ^ 128 * e3
  obtain ⟨ha, hb⟩ := lp_pair hpair
  obtain ⟨w0, w1⟩ := redV_words p
  rw [← append_qword (redV p), w0, w1, ha, hb, (qword_append _ _).1, (qword_append _ _).2, (qword_append _ _).1,
    (qword_append _ _).2]
  rw [mulW, redW]
  refine congrArg₂ (fun a b : BitVec 64 => (a ++ b : BitVec 128)) ?_ ?_
  · rw [BitVec.xor_comm (Clmul.vdword l 1) (Clmul.vdword m 0)]
  · rw [BitVec.xor_comm (Clmul.vdword l 1) (Clmul.vdword m 0), red_shuffle]

/-! ## The whole -/

/-- The product of `y` and the key of which the arguments are the vectors'
bytes, `v` the product of the sums of all the doublewords. -/
def prodV (y k0l k0h k1l k1h k2l k2h v : BitVec 128) : BitVec 128 :=
  let u := u1F y
  let p0 := vecs y k0l k0h
  let p1 := vecs u k1l k1h
  let p2 := vecs (u2F y u) k2l k2h
  redV (asm (fix p0.a p2.a) (fix p0.b p2.b) (fix p1.a (psrlq p2.a 32)) (fix p1.b (psrlq p2.b 32)) v)

theorem vec_dwords (v : BitVec 128) : lp v = lp (dword v 0) + X ^ 32 * lp (dword v 1) + X ^ 64 * (lp (dword v 2) +
    X ^ 32 * lp (dword v 3)) := by
  rw [lp_vec, lp_qword, lp_qword]

/-- A quadword of a vector's products. -/
theorem quad_ok {w K U KU q s : BitVec 128} {j i : Nat} (hj : j < 2) {o : Nat}
    (hq0 : lp (dword q (2 * j)) = lp (word w (2 * o)) * lp (word K (2 * o)))
    (hq1 : lp (dword q (2 * j + 1)) = lp (word w (2 * o + 1)) * lp (word K (2 * o + 1)))
    (hs : lp (dword s (2 * j)) = lp (word U i) * lp (word KU i))
    (hU : word U i = word w (2 * o) ^^^ word w (2 * o + 1)) (hKU : word KU i = word K (2 * o) ^^^ word K (2 * o + 1)) :
    lp (qword (fix q s) j) = lp (dword w o) * lp (dword K o) := by
  rw [fix_ok hj hq0 hq1 (by rw [hs, hU, hKU, lp_xor, lp_xor]), lp_dword w o, lp_dword K o]

theorem prodV_ok {y1 y0 h1 h0 : BitVec 64} {y K v : BitVec 128} (hy : y = y1 ++ y0)
    (hk : K = keyW1 h1 h0 ++ keyW0 h1 h0)
    (hv : lp (qword v 0) = (lp (dword y 0) + lp (dword y 2) + lp (dword y 1) + lp (dword y 3)) *
      (lp (dword K 0) + lp (dword K 2) + lp (dword K 1) + lp (dword K 3))) :
    prodV y (kbl K) (kbh K) (kbl (u1F K)) (kbh (u1F K)) (kbl (u2F K (u1F K))) (kbh (u2F K (u1F K))) v =
      Spec.Gcm.mul (y1 ++ y0 : BitVec 128) (h1 ++ h0 : BitVec 128) := by
  obtain ⟨a0, b0⟩ := vecs_ok (w := y) (keyB K)
  obtain ⟨a1, b1⟩ := vecs_ok (w := u1F y) (keyB (u1F K))
  obtain ⟨a2, b2⟩ := vecs_ok (w := u2F y (u1F y)) (keyB (u2F K (u1F K)))
  obtain ⟨uy0, uy1, uy2, uy3⟩ := dword_u1 y
  obtain ⟨uk0, uk1, uk2, uk3⟩ := dword_u1 K
  have wy := fun {j : Nat} (hj : j < 4) => word_u2 y (u1F y) hj
  have wk := fun {j : Nat} (hj : j < 4) => word_u2 K (u1F K) hj
  have sh : ∀ (s : BitVec 128) {j : Nat}, j < 2 → dword (psrlq s 32) (2 * j) = dword s (2 * j + 1) :=
    fun s _ hj => dword_psrlq32 s hj
  refine redV_ok ?_
  rw [show lp y0 + X ^ 64 * lp y1 = lp y by rw [hy]; exact (lp_append y1 y0).symm,
    show lp (keyW0 h1 h0) + X ^ 64 * lp (keyW1 h1 h0) = lp K by rw [hk]; exact (lp_append _ _).symm, vec_dwords y, vec_dwords K]
  refine asm_ok ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hv
  · exact quad_ok (j := 0) (o := 0) (by decide) (a0 0 (by decide)) (a0 1 (by decide)) (a2 0 (by decide))
      (wy (j := 0) (by decide)).1 (wk (j := 0) (by decide)).1
  · exact quad_ok (j := 1) (o := 1) (by decide) (a0 2 (by decide)) (a0 3 (by decide)) (a2 2 (by decide))
      (wy (j := 1) (by decide)).1 (wk (j := 1) (by decide)).1
  · exact quad_ok (j := 0) (o := 2) (by decide) (b0 0 (by decide)) (b0 1 (by decide)) (b2 0 (by decide))
      (wy (j := 2) (by decide)).1 (wk (j := 2) (by decide)).1
  · exact quad_ok (j := 1) (o := 3) (by decide) (b0 2 (by decide)) (b0 3 (by decide)) (b2 2 (by decide))
      (wy (j := 3) (by decide)).1 (wk (j := 3) (by decide)).1
  · rw [quad_ok (j := 0) (o := 0) (by decide) (a1 0 (by decide)) (a1 1 (by decide))
      ((congrArg lp (sh _ (by decide))).trans (a2 1 (by decide))) (wy (j := 0) (by decide)).2 (wk (j := 0) (by decide)).2,
      uy0, uk0, lp_xor, lp_xor]
  · rw [quad_ok (j := 1) (o := 1) (by decide) (a1 2 (by decide)) (a1 3 (by decide))
      ((congrArg lp (sh _ (by decide))).trans (a2 3 (by decide))) (wy (j := 1) (by decide)).2 (wk (j := 1) (by decide)).2,
      uy1, uk1, lp_xor, lp_xor]
  · rw [quad_ok (j := 0) (o := 2) (by decide) (b1 0 (by decide)) (b1 1 (by decide))
      ((congrArg lp (sh _ (by decide))).trans (b2 1 (by decide))) (wy (j := 2) (by decide)).2 (wk (j := 2) (by decide)).2,
      uy2, uk2, lp_xor, lp_xor]
  · rw [quad_ok (j := 1) (o := 3) (by decide) (b1 2 (by decide)) (b1 3 (by decide))
      ((congrArg lp (sh _ (by decide))).trans (b2 3 (by decide))) (wy (j := 3) (by decide)).2 (wk (j := 3) (by decide)).2,
      uy3, uk3, lp_xor, lp_xor]

/-! ## A block's bytes reversed -/

def revV (a : BitVec 128) : BitVec 128 :=
  shufDwords (shufHighWords (shufLowWords (por (psrlq (pxor a (pand a c00ff)) 8) (psllq (pand a c00ff) 8)) 0x1b) 0x1b) 0x4e

theorem word_low (v : BitVec 128) {i : Nat} (hi : i < 8) :
    word (shufLowWords v 0x1b) i = if i < 4 then word v (3 - i) else word v i := by
  rw [shufLowWords, word_ofWords _ hi]
  split
  · have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  · rfl

theorem word_high (v : BitVec 128) {i : Nat} (hi : i < 8) :
    word (shufHighWords v 0x1b) i = if i < 4 then word v i else word v (11 - i) := by
  rw [shufHighWords, word_ofWords _ hi]
  split
  · rfl
  · have h : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl

theorem word_swap (v : BitVec 128) {i : Nat} (hi : i < 8) : word (shufDwords v 0x4e) i = word v ((i + 4) % 8) := by
  have hd : dword (shufDwords v 0x4e) (i / 2) = dword v ((i / 2 + 2) % 4) := by
    have h : i / 2 = 0 ∨ i / 2 = 1 ∨ i / 2 = 2 ∨ i / 2 = 3 := by omega
    rcases h with e | e | e | e <;> rw [e]
    · exact dword_ofDwords_0 ..
    · exact dword_ofDwords_1 ..
    · exact dword_ofDwords_2 ..
    · exact dword_ofDwords_3 ..
  rw [word_eq_dword, hd, word_eq_dword v, show (i + 4) % 8 / 2 = (i / 2 + 2) % 4 by omega,
    show (i + 4) % 8 % 2 = i % 2 by omega]

theorem word_rev (a : BitVec 128) {i : Nat} (hi : i < 8) :
    word (revV a) i = word a (7 - i) >>> 8 ||| word a (7 - i) <<< 8 := by
  have hs : ∀ j < 8, word (por (psrlq (pxor a (pand a c00ff)) 8) (psllq (pand a c00ff) 8)) j =
      word a j >>> 8 ||| word a j <<< 8 := fun j hj => by
    rw [← word_down a hj, ← word_up a hj]
    apply BitVec.eq_of_getLsbD_eq
    intro p hp
    rw [BitVec.getLsbD_or, getLsbD_word _ _ _ hp, getLsbD_word _ _ _ hp, getLsbD_word _ _ _ hp, por_eq, BitVec.getLsbD_or]
  rw [revV, word_swap _ hi, word_high _ (by omega)]
  by_cases h : i < 4
  · rw [ite_eq_right (by omega), word_low _ (by omega), ite_eq_right (by omega), hs _ (by omega),
      show 11 - (i + 4) % 8 = 7 - i by omega]
  · rw [ite_eq_left (by omega), word_low _ (by omega), ite_eq_left (by omega), hs _ (by omega),
      show 3 - (i + 4) % 8 = 7 - i by omega]

theorem byte_word (v : BitVec 128) (i p : Nat) (hp : p < 8) :
    (byte v i).getLsbD p = (word v (i / 2)).getLsbD (8 * (i % 2) + p) := by
  rw [byte, BitVec.getLsbD_extractLsb', getLsbD_word _ _ _ (by omega), decide_eq_true hp, Bool.true_and]
  exact congrArg _ (by omega)

theorem revV_byte (a : BitVec 128) {i : Nat} (hi : i < 16) : byte (revV a) i = byte a (15 - i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [byte_word _ _ _ hp, byte_word _ _ _ hp, word_rev a (by omega), BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, show (15 - i) / 2 = 7 - i / 2 by omega]
  rcases (by omega : i % 2 = 0 ∨ i % 2 = 1) with h | h
  · rw [h, show (15 - i) % 2 = 1 by omega]
    simp [show p < 8 from hp]
  · rw [h, show (15 - i) % 2 = 0 by omega]
    simp [show 8 + p < 16 by omega, BitVec.getLsbD_of_ge (word a (7 - i / 2)) (8 + (8 + p)) (by omega)]

/-- A block, loaded and reversed. -/
theorem revV_block (m : Mem) (p : Addr) : revV (m.readW p 128) = Spec.Gcm.blockAt m p := by
  rw [blockAt_eq, pshufb_rev]
  exact ext_byte fun i hi => by rw [revV_byte _ hi, byte_ofBytes _ hi]

end VG.Proof.Gcm.X86
