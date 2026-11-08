module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ML-KEM on PPC64LE: the words of vectors

What the vector NTT needs of the vector instructions, word by word (`vword`,
most significant first): the words of a vector built word by word
(`vword_ofVWords`), of the doubleword products of `vmuleuw`/`vmulouw`
(`vword_dwords`), of a `vperm` whose control selects whole words
(`vword_perm`), and the order of four `u32`s of memory after `lxvd2x` and
before `stxvd2x` (`vword_row`, `store_byte`): words `1, 0, 3, 2`. As in
`Proof/ChaCha20/PPC64LE/Vmx4/Chunk.lean`.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.Lanes

open VG VG.PPC64LE

theorem vword_ofVWords (f : Nat → BitVec 32) {i : Nat} (hi : i < 4) : vword (ofVWords f) i = f i := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [ofVWords, vword, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.ofNat_eq_ofNat,
    BitVec.getLsbD_zero, Bool.false_or]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  all_goals simp (disch := omega) only [decide_eq_true, decide_eq_false, BitVec.getLsbD_of_ge,
    Bool.true_and, Bool.false_and, Bool.and_false, Bool.and_true, Bool.not_false, Bool.not_true,
    Bool.false_or, Bool.or_false]
  all_goals exact congrArg _ (by omega)

/-- The word-wise addition of `vadduwm` is `ofVWords` of the sums. -/
theorem add_eq (x y : BitVec 128) :
    (List.range 4).foldl (fun a i => a ||| ((vword x i + vword y i).setWidth 128 <<< (32 * (3 - i)))) 0 =
      ofVWords fun i => vword x i + vword y i := rfl

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

/-- A word of a vector as its bytes, most significant first. -/
theorem vword_bytes (x : BitVec 128) {p : Nat} (hp : p < 4) :
    vword x p = vbyte x (4 * p) ++ vbyte x (4 * p + 1) ++ vbyte x (4 * p + 2) ++ vbyte x (4 * p + 3) := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [vword, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true,
    Bool.true_and]
  by_cases h1 : b < 8
  · simp only [h1, ite_true, decide_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)
  by_cases h2 : b - 8 < 8
  · simp only [h1, h2, ite_true, ite_false, decide_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)
  by_cases h3 : b - 8 - 8 < 8
  · simp only [h1, h2, h3, ite_true, ite_false, decide_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)
  · simp only [h1, h2, h3, ite_false, show b - 8 - 8 - 8 < 8 by omega, decide_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)

/-- The result of `vperm` on `n` and `m` with the control `c`. -/
def perm (n m c : BitVec 128) : BitVec 128 :=
  ofVBytes fun i =>
    let j := (vbyte c i).toNat % 32
    if j < 16 then vbyte n j else vbyte m (j - 16)

theorem exec_perm (d n m c : VReg) (s : State) :
    exec (.vop (.perm d n m c)) s = some (s.writeV d (perm (s.vpr n) (s.vpr m) (s.vpr c))) := rfl

/-- A `vperm` whose control selects word `q` of the concatenation of its
operands for word `p`. -/
theorem vword_perm (n m c : BitVec 128) {p q : Nat} (hp : p < 4) (hq : q < 8)
    (hc : ∀ t < 4, (vbyte c (4 * p + t)).toNat % 32 = 4 * q + t) :
    vword (perm n m c) p = if q < 4 then vword n q else vword m (q - 4) := by
  rw [vword_bytes _ hp, perm, vbyte_packed _ (by omega), vbyte_packed _ (by omega),
    vbyte_packed _ (by omega), vbyte_packed _ (by omega)]
  have h0 := hc 0 (by decide); have h1 := hc 1 (by decide)
  have h2 := hc 2 (by decide); have h3 := hc 3 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [h0, h1, h2, h3]
  by_cases hq4 : q < 4
  · rw [ite_eq_left hq4, vword_bytes _ hq4]
    simp only [show 4 * q < 16 by omega, show 4 * q + 1 < 16 by omega,
      show 4 * q + 2 < 16 by omega, show 4 * q + 3 < 16 by omega, ite_true]
  · rw [ite_eq_right hq4, vword_bytes _ (by omega)]
    simp only [show ¬ 4 * q < 16 by omega, show ¬ 4 * q + 1 < 16 by omega,
      show ¬ 4 * q + 2 < 16 by omega, show ¬ 4 * q + 3 < 16 by omega, ite_false,
      show 4 * q - 16 = 4 * (q - 4) by omega, show 4 * q + 1 - 16 = 4 * (q - 4) + 1 by omega,
      show 4 * q + 2 - 16 = 4 * (q - 4) + 2 by omega, show 4 * q + 3 - 16 = 4 * (q - 4) + 3 by omega]

theorem ext_vword {x y : BitVec 128} (h : ∀ p < 4, vword x p = vword y p) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e := congrArg (BitVec.getLsbD · (i % 32)) (h (3 - i / 32) (by omega))
  simp only [vword, BitVec.getLsbD_extractLsb', show i % 32 < 32 by omega, decide_true,
    Bool.true_and] at e
  rwa [show 32 * (3 - (3 - i / 32)) + i % 32 = i by omega] at e

/-! ## Memory -/

/-- Equal words from equal bytes. -/
theorem ext_bytes32 {x y : BitVec 32} (h : ∀ t < 4, x.extractLsb' (8 * t) 8 = y.extractLsb' (8 * t) 8) :
    x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have e := congrArg (BitVec.getLsbD · (b % 8)) (h (b / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show b % 8 < 8 by omega, decide_true, Bool.true_and] at e
  rwa [show 8 * (b / 8) + b % 8 = b by omega] at e

theorem vword_byte (x : BitVec 128) (p t : Nat) (ht : t < 4) :
    (vword x p).extractLsb' (8 * t) 8 = x.extractLsb' (8 * (4 * (3 - p) + t)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [vword, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
    show 8 * t + b < 32 by omega]
  exact congrArg x.getLsbD (by omega)

theorem swap_byte (y : BitVec 128) {k : Nat} (hk : k < 16) :
    (swapDwords y).extractLsb' (8 * k) 8 = y.extractLsb' (8 * (if k < 8 then k + 8 else k - 8)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and]
  rw [getLsbD_swapDwords _ (by omega)]
  exact congrArg y.getLsbD (by split <;> split <;> omega)

/-- `lxvd2x` puts the words of a row of memory in the order 1, 0, 3, 2. -/
theorem vword_row (m : Mem) (a : Addr) {p : Nat} (hp : p < 4) :
    vword (swapDwords (m.read a 16)) p = m.readW (a + BitVec.ofNat 64 (4 * (p ^^^ 1))) 32 := by
  apply ext_bytes32
  intro t ht
  rw [vword_byte _ _ _ ht, swap_byte _ (by omega), Mem.extractLsb'_read _ _ (by split <;> omega),
    ← Mem.readW_byte _ _ ht, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 3
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right, Nat.reduceXor] <;> omega

/-- Byte `k` of what `stxvd2x` stores of a vector of words `w₁, w₀, w₃, w₂`
(most significant first): byte `k % 4` of word `k / 4`. -/
theorem store_byte (x : BitVec 128) {k : Nat} (hk : k < 16) :
    (swapDwords x).extractLsb' (8 * k) 8 =
      (vword x ((k / 4) ^^^ 1)).extractLsb' (8 * (k % 4)) 8 := by
  rw [swap_byte _ hk, vword_byte _ _ _ (by omega)]
  congr 2
  rcases (by omega : k / 4 = 0 ∨ k / 4 = 1 ∨ k / 4 = 2 ∨ k / 4 = 3) with h | h | h | h <;>
    simp (disch := omega) only [h, ↓ite_eq_left, ↓ite_eq_right, Nat.reduceXor] <;> omega

end VG.Proof.MlKem.PPC64LE.Lanes
