module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# PPC64LE: the words of vectors

What proofs of vector code need of its words (`vword`, most significant
first): a vector built word by word (`vword_ofVWords`) and equal words
(`ext_vword`); `vperm` whose control selects whole words (`permV`,
`vword_permV`); the words of two doublewords, as `vmuleuw` and `vmulouw`
leave products (`vword_dwords`, `vword_dw_hi`); and the order of four
`u32`s of memory in a vector: `lxvd2x` puts the word at `a + 4·(e XOR 1)`
in word `e` (`vword_load`), and `stxvd2x` writes word `e` there
(`readW_store`).
-/

@[expose] public section

namespace VG.PPC64LE

/-! ## Words of vectors -/

theorem wordTerm_bit (f : Nat → BitVec 32) {k j r : Nat} (hk : k < 4) (hj : j < 4) (hr : r < 32) :
    ((f k).setWidth 128 <<< (32 * (3-k))).getLsbD (32*j+r) =
      if j = 3-k then (f k).getLsbD r else false := by
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j = 3-k
  · subst j
    simp only [show ¬32*(3-k)+r < 32*(3-k) by omega, decide_false,
      Bool.not_false, Nat.add_sub_cancel_left, show 32*(3-k)+r < 128 by omega,
      show r < 128 by omega, decide_true, Bool.true_and, ite_true]
  · have h' : 32*j+r < 32*(3-k) ∨ 32 ≤ 32*j+r-32*(3-k) := by omega
    rcases h' with h' | h' <;> simp [h, h']

theorem word_bit (f : Nat → BitVec 32) {j r : Nat} (hj : j < 4) (hr : r < 32) :
    ∀ k, k ≤ 4 →
    ((List.range k).foldl (fun x i => x ||| ((f i).setWidth 128 <<< (32*(3-i)))) (0#128)).getLsbD (32*j+r) =
      if 3-j < k then (f (3-j)).getLsbD r else false
  | 0, _ => by simp
  | k+1, hk => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      BitVec.getLsbD_or, word_bit f hj hr k (by omega), wordTerm_bit f (by omega) hj hr]
    by_cases h : 3-j < k
    · simp [h, show 3-j < k+1 by omega, show j ≠ 3-k by omega]
    · by_cases e : j = 3-k
      · rw [ite_eq_right h, ite_eq_left e, ite_eq_left (show 3-j < k+1 by omega), Bool.false_or]
        exact congrArg (fun i => (f i).getLsbD r) (by omega)
      · simp [h, e, show ¬3-j < k+1 by omega]

theorem vword_ofVWords (f : Nat → BitVec 32) {i : Nat} (hi : i < 4) : vword (ofVWords f) i = f i := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  simp only [vword, BitVec.getLsbD_extractLsb', hr, decide_true, Bool.true_and]
  have := word_bit f (j := 3-i) (by omega) hr 4 (by omega)
  simp only [show 3-(3-i) = i by omega, hi, ite_true] at this
  exact this

theorem ext_vword {a b : BitVec 128} (h : ∀ i < 4, vword a i = vword b i) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have he := congrArg (BitVec.getLsbD · (j % 32)) (h (3-j/32) (by omega))
  simp only [vword, BitVec.getLsbD_extractLsb', show j % 32 < 32 by omega,
    decide_true, Bool.true_and] at he
  rwa [show 32*(3-(3-j/32)) + j%32 = j by omega] at he

/-- `vperm`'s result. -/
def permV (n m c : BitVec 128) : BitVec 128 := ofVBytes fun i =>
  let j := (vbyte c i).toNat % 32
  if j < 16 then vbyte n j else vbyte m (j - 16)

/-- Lane `i` of `vperm` is word `k` of `VA || VB` when the control's bytes
`4i … 4i+3` select its bytes. -/
theorem vword_permV (n m c : BitVec 128) {i k : Nat} (hi : i < 4) (hk : k < 8)
    (hc : ∀ t < 4, (vbyte c (4*i+t)).toNat % 32 = 4*k+t) :
    vword (permV n m c) i = if k < 4 then vword n k else vword m (k-4) := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  simp only [vword, BitVec.getLsbD_extractLsb', hr, decide_true, Bool.true_and]
  have e : 32*(3-i)+r = 8*(15-(4*i+(3-r/8)))+r%8 := by omega
  rw [e, permV, getLsbD_packed _ (by omega) (by omega), show 15-(15-(4*i+(3-r/8))) = 4*i+(3-r/8) by omega]
  simp only [hc _ (by omega : 3 - r/8 < 4)]
  split <;> split
  · simp only [vbyte, BitVec.getLsbD_extractLsb', show r % 8 < 8 by omega, hr, decide_true, Bool.true_and]
    exact congrArg _ (by omega)
  · omega
  · omega
  · simp only [vbyte, BitVec.getLsbD_extractLsb', show r % 8 < 8 by omega, hr, decide_true, Bool.true_and]
    exact congrArg _ (by omega)

/-- The high words of two doublewords. -/
theorem vword_dw_hi (a b : BitVec 64) :
    (vword (a ++ b) 0).toNat = a.toNat / 2^32 ∧ (vword (a ++ b) 2).toNat = b.toNat / 2^32 := by
  constructor <;>
  · simp only [vword, BitVec.extractLsb'_toNat, BitVec.toNat_append, Nat.shiftRight_eq_div_pow]
    have := a.isLt; have := b.isLt
    rw [← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
    omega

/-- The words of two doublewords. -/
theorem vword_dwords (a b : BitVec 64) {j : Nat} (hj : j < 4) :
    vword (a ++ b : BitVec 128) j =
      if j = 0 then a.extractLsb' 32 32 else if j = 1 then a.extractLsb' 0 32
      else if j = 2 then b.extractLsb' 32 32 else b.extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  simp only [vword, BitVec.getLsbD_extractLsb', ht, decide_true, Bool.true_and, BitVec.getLsbD_append]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right, Nat.reduceSub, Nat.reduceMul,
      BitVec.getLsbD_extractLsb', decide_true, Bool.true_and, ht] <;>
    exact congrArg _ (by omega)

/-! ## `lxvd2x` and `stxvd2x` -/

/-- Bit `i` of a little-endian read is bit `i % 8` of byte `i / 8`. -/
theorem getLsbD_read (m : Mem) (a : Addr) {n i : Nat} (hi : i < 8 * n) :
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8) := by
  have h := congrArg (BitVec.getLsbD · (i % 8)) (Mem.extractLsb'_read m a (n := n) (j := i / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, decide_true, Bool.true_and] at h
  rw [← h]
  exact congrArg _ (by omega)

/-- Bytes `k … k + l` of a read. -/
theorem read_extract (m : Mem) (a : Addr) {n k l : Nat} (h : k + l ≤ n) :
    (m.read a n).extractLsb' (8 * k) (8 * l) = m.read (a + BitVec.ofNat 64 k) l := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  rw [BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and, getLsbD_read _ _ (by omega),
    getLsbD_read _ _ hr, BitVec.add_assoc, ← BitVec.ofNat_add, show (8 * k + r) / 8 = k + r / 8 by omega,
    show (8 * k + r) % 8 = r % 8 by omega]

theorem getLsbD_swap (x : BitVec 128) {p : Nat} (hp : p < 128) :
    (swapDwords x).getLsbD p = x.getLsbD (if p < 64 then p + 64 else p - 64) := by
  simp only [swapDwords, vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : p < 64
  · simp only [h, ite_true, decide_true, Bool.true_and]; exact congrArg _ (by omega)
  · simp only [h, ite_false, show p - 64 < 64 by omega, decide_true, Bool.true_and]; exact congrArg _ (by omega)

theorem xor1_lt {e : Nat} (he : e < 4) : e ^^^ 1 < 4 := by
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;> decide

theorem xor1_xor1 (e : Nat) : (e ^^^ 1) ^^^ 1 = e := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- Lane `e` of `swapDwords x` is word `e XOR 1` of `x` from its low end. -/
theorem vword_swap (x : BitVec 128) {e : Nat} (he : e < 4) :
    vword (swapDwords x) e = x.extractLsb' (32 * (e ^^^ 1)) 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  simp only [vword, BitVec.getLsbD_extractLsb', hr, decide_true, Bool.true_and]
  rw [getLsbD_swap _ (by omega)]
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [Nat.reduceXor]
    split <;> first | omega | exact congrArg _ (by omega)

/-- Lane `e` of a `lxvd2x` of `[a, a + 16)`. -/
theorem vword_load (m : Mem) (a : Addr) {e : Nat} (he : e < 4) :
    vword (swapDwords (m.read a 16)) e = m.readW (a + BitVec.ofNat 64 (4 * (e ^^^ 1))) 32 := by
  have hk := xor1_lt he
  rw [vword_swap _ he, show 32 * (e ^^^ 1) = 8 * (4 * (e ^^^ 1)) by omega,
    read_extract m a (n := 16) (k := 4 * (e ^^^ 1)) (l := 4) (by omega)]
  simp only [Mem.readW, BitVec.setWidth_eq]

/-- The word at `a + 4k` after a `stxvd2x` of `v` to `[a, a + 16)`. -/
theorem readW_store (m : Mem) (a : Addr) (v : BitVec 128) {k : Nat} (hk : k < 4) :
    (m.write a 16 (swapDwords v)).readW (a + BitVec.ofNat 64 (4 * k)) 32 = vword v (k ^^^ 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  simp only [Mem.readW, BitVec.setWidth_eq]
  rw [getLsbD_read _ _ (by omega)]
  simp only [Mem.write]
  rw [show a + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 (r / 8) - a = BitVec.ofNat 64 (4 * k + r / 8) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left]]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [show 4 * k + r / 8 < 16 by omega, ite_true, BitVec.getLsbD_extractLsb', show r % 8 < 8 by omega,
    decide_true, Bool.true_and, vword, hr]
  rw [getLsbD_swap _ (by omega)]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [Nat.reduceXor]
    split <;> first | omega | exact congrArg _ (by omega)

end VG.PPC64LE
