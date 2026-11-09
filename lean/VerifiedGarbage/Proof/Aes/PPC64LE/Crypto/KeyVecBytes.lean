module

public import VerifiedGarbage.Proof.Aes.KeyWords
public import VerifiedGarbage.TCB.PPC64LE.Simd
public import VerifiedGarbage.Impl.Aes.PPC64LE.Crypto.ExpandKey
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: the vector key loops' byte arithmetic is independent of the code that runs it.
/-! # Four key-schedule words in a vector register

`Rk f j v`: byte `i` of `v` (from the most significant) is byte `3 − i % 4`
of `f (j + 3 − i / 4)`, so that `v = f (j+3) ‖ f (j+2) ‖ f (j+1) ‖ f j`,
the 16 bytes `f j … f (j+3)` as one little-endian number. The next four words
are `temp` in each word XORed with the prefix XORs of these (`step_rk`).
-/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Proof.Aes.KeyWords (sub32 extract_xor sub32_byte Good extract_cat rot_cat)

/-- Byte `i` of `f (j+3) ‖ … ‖ f j`. -/
def kb (f : Nat → BitVec 32) (j i : Nat) : BitVec 8 := (f (j + 3 - i / 4)).extractLsb' (8 * (3 - i % 4)) 8

def Rk (f : Nat → BitVec 32) (j : Nat) (v : BitVec 128) : Prop := ∀ i < 16, vbyte v i = kb f j i

/-- `vsldoi d x z sh` with `z = 0`. -/
def shl (x : BitVec 128) (sh : Nat) : BitVec 128 := ((x ++ (0 : BitVec 128)) <<< (8 * sh)).extractLsb' 128 128

/-- `prefixXor`'s value. -/
def pfx (x : BitVec 128) : BitVec 128 := (x ^^^ shl x 4) ^^^ shl (x ^^^ shl x 4) 8

/-- `f j ⊕ … ⊕ f (j + k)`. -/
def pre (f : Nat → BitVec 32) (j : Nat) : Nat → BitVec 32
  | 0 => f j
  | k + 1 => pre f j k ^^^ f (j + k + 1)

theorem vbyte_sldoi (n m : BitVec 128) {sh i : Nat} (hsh : sh < 16) (hi : i < 16) :
    vbyte (((n ++ m) <<< (8 * sh)).extractLsb' 128 128) i =
      if i + sh < 16 then vbyte n (i + sh) else vbyte m (i + sh - 16) := by
  by_cases hc : i + sh < 16
  · rw [ite_eq_left hc]
    apply BitVec.eq_of_getLsbD_eq; intro r hr
    simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, hr,
      decide_true, Bool.true_and]
    simp only [show 128 + (8 * (15 - i) + r) < 128 + 128 by omega,
      show ¬ 128 + (8 * (15 - i) + r) < 8 * sh by omega, show ¬ 128 + (8 * (15 - i) + r) - 8 * sh < 128 by omega,
      decide_true, decide_false, Bool.not_false, Bool.true_and, ite_false,
      show 8 * (15 - i) + r < 128 by omega, Bool.true_and]
    exact congrArg n.getLsbD (by omega)
  · rw [ite_eq_right hc]
    apply BitVec.eq_of_getLsbD_eq; intro r hr
    simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, hr,
      decide_true, Bool.true_and]
    simp only [show 128 + (8 * (15 - i) + r) < 128 + 128 by omega,
      show ¬ 128 + (8 * (15 - i) + r) < 8 * sh by omega, show 128 + (8 * (15 - i) + r) - 8 * sh < 128 by omega,
      decide_true, decide_false, Bool.not_false, Bool.true_and, ite_true,
      show 8 * (15 - i) + r < 128 by omega, Bool.true_and]
    exact congrArg m.getLsbD (by omega)

theorem vbyte_zero (i : Nat) : vbyte (0 : BitVec 128) i = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp [vbyte]

theorem vbyte_xor (a b : BitVec 128) (i : Nat) : vbyte (a ^^^ b) i = vbyte a i ^^^ vbyte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp [vbyte, hr]

theorem vbyte_shl (x : BitVec 128) {sh i : Nat} (hsh : sh < 16) (hi : i < 16) :
    vbyte (shl x sh) i = if i + sh < 16 then vbyte x (i + sh) else 0#8 := by
  rw [shl, vbyte_sldoi _ _ hsh hi, vbyte_zero]

theorem vbyte_pfx (x : BitVec 128) {i : Nat} (hi : i < 16) :
    vbyte (pfx x) i = (vbyte x i ^^^ (if i + 4 < 16 then vbyte x (i + 4) else 0#8)) ^^^
      (if i + 8 < 16 then vbyte x (i + 8) ^^^ (if i + 12 < 16 then vbyte x (i + 12) else 0#8) else 0#8) := by
  rw [pfx, vbyte_xor, vbyte_xor, vbyte_shl _ (by decide) hi,
    vbyte_shl _ (by decide) hi]
  by_cases h8 : i + 8 < 16
  · rw [ite_eq_left h8, ite_eq_left h8, vbyte_xor, vbyte_shl _ (by decide) (by omega),
      show i + 8 + 4 = i + 12 by omega]
  · rw [ite_eq_right h8, ite_eq_right h8]

/-- Bytes of `Rk` four apart: the same byte of the word before. -/
theorem rk_byte {f : Nat → BitVec 32} {j : Nat} {v : BitVec 128} (h : Rk f j v) {c p : Nat}
    (hc : c < 4) (hp : p < 4) : vbyte v (4 * c + p) = (f (j + 3 - c)).extractLsb' (8 * (3 - p)) 8 := by
  rw [h _ (by omega), kb, show (4 * c + p) / 4 = c by omega, show (4 * c + p) % 4 = p by omega]

theorem extract_pre (f : Nat → BitVec 32) (j k q : Nat) :
    (pre f j (k + 1)).extractLsb' q 8 = (pre f j k).extractLsb' q 8 ^^^ (f (j + k + 1)).extractLsb' q 8 := by
  rw [pre, extract_xor]

theorem pfx_byte {f : Nat → BitVec 32} {j : Nat} {v : BitVec 128} (h : Rk f j v) {i : Nat} (hi : i < 16) :
    vbyte (pfx v) i = (pre f j (3 - i / 4)).extractLsb' (8 * (3 - i % 4)) 8 := by
  obtain ⟨c, p, hc, hp, rfl⟩ : ∃ c p, c < 4 ∧ p < 4 ∧ i = 4 * c + p := ⟨i / 4, i % 4, by omega, by omega, by omega⟩
  rw [vbyte_pfx _ hi, show (4 * c + p) / 4 = c by omega, show (4 * c + p) % 4 = p by omega]
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      show 4 * 0 + p + 4 = 4 * 1 + p by omega, show 4 * 0 + p + 8 = 4 * 2 + p by omega,
      show 4 * 0 + p + 12 = 4 * 3 + p by omega, rk_byte h (by decide) hp, rk_byte h (by decide) hp,
      rk_byte h (by decide) hp, rk_byte h (by decide) hp, extract_pre, extract_pre, extract_pre]
    simp only [pre, Nat.add_zero, show j + 3 - 0 = j + 2 + 1 by omega, show j + 3 - 1 = j + 1 + 1 by omega,
      show j + 3 - 2 = j + 0 + 1 by omega, show j + 3 - 3 = j by omega]
    ac_rfl
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right (by omega),
      show 4 * 1 + p + 4 = 4 * 2 + p by omega, show 4 * 1 + p + 8 = 4 * 3 + p by omega,
      rk_byte h (by decide) hp, rk_byte h (by decide) hp, rk_byte h (by decide) hp,
      show 3 - 1 = 1 + 1 by rfl, extract_pre, extract_pre, BitVec.xor_zero]
    simp only [pre, show j + 3 - 1 = j + 1 + 1 by omega, show j + 3 - 2 = j + 0 + 1 by omega,
      show j + 3 - 3 = j by omega, Nat.add_zero]
    ac_rfl
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), show 4 * 2 + p + 4 = 4 * 3 + p by omega,
      rk_byte h (by decide) hp, rk_byte h (by decide) hp, show 3 - 2 = 0 + 1 by rfl, extract_pre,
      BitVec.xor_zero]
    simp only [pre, show j + 3 - 2 = j + 0 + 1 by omega, show j + 3 - 3 = j by omega]
    ac_rfl
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), rk_byte h (by decide) hp, BitVec.xor_zero,
      BitVec.xor_zero]
    simp only [pre, show j + 3 - 3 = j by omega, show 3 - 3 = 0 by rfl]

/-- The next four words, from `temp` in every word of `y`. -/
theorem step_rk {f : Nat → BitVec 32} {j nk : Nat} {v y : BitVec 128} {t : BitVec 32} (h : Rk f j v)
    (hy : ∀ i < 16, vbyte y i = t.extractLsb' (8 * (3 - i % 4)) 8)
    (hnext : ∀ k < 4, f (j + nk + k) = t ^^^ pre f j k) : Rk f (j + nk) (pfx v ^^^ y) := by
  intro i hi
  rw [vbyte_xor, pfx_byte h hi, hy i hi, kb, show j + nk + 3 - i / 4 = j + nk + (3 - i / 4) by omega,
    hnext _ (by omega), extract_xor, BitVec.xor_comm]

/-- The recurrence, four words at a time: `w[j+nk]` is `w[j] ⊕ temp`, the
next three `w[j+nk+k] = w[j+k] ⊕ w[j+nk+k−1]`. -/
theorem next_pre {f : Nat → BitVec 32} {j nk : Nat} {t : BitVec 32} (h0 : f (j + nk) = f j ^^^ t)
    (h : ∀ k, 0 < k → k < 4 → f (j + nk + k) = f (j + k) ^^^ f (j + nk + k - 1)) :
    ∀ k < 4, f (j + nk + k) = t ^^^ pre f j k
  | 0, _ => by rw [Nat.add_zero, h0, pre, BitVec.xor_comm]
  | k + 1, hk => by
    rw [h (k + 1) (by omega) hk, show j + nk + (k + 1) - 1 = j + nk + k by omega, next_pre h0 h k (by omega), pre,
      show j + (k + 1) = j + k + 1 by omega]
    ac_rfl

/-! ## `temp` in every word -/

theorem bytes_cat (x : BitVec 32) :
    x = x.extractLsb' 24 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 0 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hi' : i < 32 := hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ 24 ≤ i) with h | h | h | h <;>
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right] <;>
    (rw [decide_eq_true (by omega), Bool.true_and]; exact congrArg _ (by omega))


theorem rotr8_byte (x : BitVec 32) {q : Nat} (hq : q < 4) :
    (x.rotateRight 8).extractLsb' (8 * q) 8 = x.extractLsb' (8 * ((q + 1) % 4)) 8 := by
  have e := bytes_cat x
  obtain ⟨e0, e1, e2, e3⟩ := extract_cat (x.extractLsb' 24 8) (x.extractLsb' 16 8) (x.extractLsb' 8 8) (x.extractLsb' 0 8)
  obtain ⟨f0, f1, f2, f3⟩ := extract_cat (x.extractLsb' 0 8) (x.extractLsb' 24 8) (x.extractLsb' 16 8) (x.extractLsb' 8 8)
  rw [show x.rotateRight 8 = _ from (congrArg (·.rotateRight 8) e).trans (rot_cat _ _ _ _)]
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl
  · exact f0
  · exact f1
  · exact f2
  · exact f3

theorem rc_byte (c : BitVec 8) {q : Nat} (hq : q < 4) :
    (c.setWidth 32).extractLsb' (8 * q) 8 = if q = 0 then c else 0#8 := by
  rw [show c.setWidth 32 = 0#8 ++ 0#8 ++ 0#8 ++ c by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_zero]
    by_cases h : i < 8
    · simp [h]; omega
    · simp [h]; exact fun _ => BitVec.getLsbD_of_ge _ _ (by omega)]
  obtain ⟨e0, e1, e2, e3⟩ := extract_cat 0#8 0#8 0#8 c
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl
  · exact e0
  · exact e1
  · exact e2
  · exact e3

theorem vbyte_permSelf (t : BitVec 128) (k : BitVec 64) {i : Nat} (hi : i < 16) :
    vbyte (permSelf t (k ++ k)) i =
      let j := (vbyte (k ++ k) i).toNat % 32; if j < 16 then vbyte t j else vbyte t (j - 16) :=
  vbyte_packed _ hi

def rotIdx (p : Nat) : Nat := if p = 0 then 3 else p - 1

theorem rotCtl_idx : ∀ i < 16,
    (vbyte (Impl.Aes.PPC64LE.Crypto.rotCtl ++ Impl.Aes.PPC64LE.Crypto.rotCtl) i).toNat % 32 = rotIdx (i % 4) := by
  decide

theorem subCtl_idx : ∀ i < 16,
    (vbyte (Impl.Aes.PPC64LE.Crypto.subCtl ++ Impl.Aes.PPC64LE.Crypto.subCtl) i).toNat % 32 = i % 4 := by
  decide

theorem rcCtl_idx : ∀ i < 16,
    (vbyte (Impl.Aes.PPC64LE.Crypto.rcCtl ++ Impl.Aes.PPC64LE.Crypto.rcCtl) i).toNat % 32 =
      if i % 4 = 3 then 7 else 16 := by
  decide

/-- `vsbox`'s value. -/
def sboxV (x : BitVec 128) : BitVec 128 := ofVBytes fun i => VectorCrypto.aesSbox (vbyte x i)

theorem hi_byte (c : BitVec 8) (u : BitVec 64) : vbyte (c.setWidth 64 ++ u) 7 = c := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_setWidth, hr, decide_true,
    Bool.true_and]
  simp (disch := omega) only [↓ite_eq_right]
  rw [decide_eq_true (by omega), Bool.true_and]; exact congrArg _ (by omega)


/-- The round constant in the low byte of every word: `vperm` of the GPR
`mtvsrd` moved, and zero. -/
theorem rc_splat (c : BitVec 8) (u : BitVec 64) {i : Nat} (hi : i < 16) :
    vbyte (ofVBytes fun i =>
      let j := (vbyte (Impl.Aes.PPC64LE.Crypto.rcCtl ++ Impl.Aes.PPC64LE.Crypto.rcCtl) i).toNat % 32
      if j < 16 then vbyte (c.setWidth 64 ++ u) j else vbyte (0 : BitVec 128) (j - 16)) i =
      if i % 4 = 3 then c else 0#8 := by
  rw [vbyte_packed _ hi]
  simp only [rcCtl_idx i hi]
  split
  · rw [ite_eq_left (by decide), hi_byte]
  · rw [ite_eq_right (by decide), show 16 - 16 = 0 from rfl, vbyte_zero]

theorem rk_top {f : Nat → BitVec 32} {j : Nat} {v : BitVec 128} (h : Rk f j v) {p : Nat} (hp : p < 4) :
    vbyte v p = (f (j + 3)).extractLsb' (8 * (3 - p)) 8 := by
  rw [h p (by omega), kb, Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp, Nat.sub_zero]


theorem rot_temp {f : Nat → BitVec 32} {j : Nat} {t r : BitVec 128} {c : BitVec 8} (ht : Rk f j t)
    (hr : ∀ i < 16, vbyte r i = if i % 4 = 3 then c else 0#8) :
    ∀ i < 16, vbyte (sboxV (permSelf t (Impl.Aes.PPC64LE.Crypto.rotCtl ++ Impl.Aes.PPC64LE.Crypto.rotCtl)) ^^^ r) i =
      ((sub32 (f (j + 3))).rotateRight 8 ^^^ c.setWidth 32).extractLsb' (8 * (3 - i % 4)) 8 := by
  intro i hi
  rw [vbyte_xor, sboxV, vbyte_packed _ hi, vbyte_permSelf _ _ hi, hr i hi]
  simp only [rotCtl_idx i hi]
  have hp : i % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize i % 4 = p at hp ⊢
  rw [extract_xor, rotr8_byte _ (by omega), rc_byte _ (by omega)]
  have t0 := rk_top ht (p := 0) (by decide)
  have t1 := rk_top ht (p := 1) (by decide)
  have t2 := rk_top ht (p := 2) (by decide)
  have t3 := rk_top ht (p := 3) (by decide)
  have s0 := sub32_byte (f (j + 3)) (q := 0) (by decide)
  have s1 := sub32_byte (f (j + 3)) (q := 1) (by decide)
  have s2 := sub32_byte (f (j + 3)) (q := 2) (by decide)
  have s3 := sub32_byte (f (j + 3)) (q := 3) (by decide)
  simp only [Nat.reduceSub, Nat.reduceMul] at t0 t1 t2 t3 s0 s1 s2 s3
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3) with rfl | rfl | rfl | rfl <;>
    simp [rotIdx, t0, t1, t2, t3, s0, s1, s2, s3]


theorem sub_temp {f : Nat → BitVec 32} {j : Nat} {t : BitVec 128} (ht : Rk f j t) :
    ∀ i < 16, vbyte (sboxV (permSelf t (Impl.Aes.PPC64LE.Crypto.subCtl ++ Impl.Aes.PPC64LE.Crypto.subCtl))) i =
      (sub32 (f (j + 3))).extractLsb' (8 * (3 - i % 4)) 8 := by
  intro i hi
  rw [sboxV, vbyte_packed _ hi, vbyte_permSelf _ _ hi]
  simp only [subCtl_idx i hi]
  have hp : i % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [ite_eq_left (by omega), rk_top ht hp, sub32_byte _ (by omega)]

/-! ## The schedule in memory -/

/-- Four words of the schedule, read as one little-endian number. -/
theorem load_rk {m : Mem} {S : Addr} {f : Nat → BitVec 32} {j K : Nat} (hg : Good m S f K) (hj : j + 4 ≤ K)
    (hK : K ≤ 60) : Rk f j (m.read (S + BitVec.ofNat 64 (4 * j)) 16) := by
  intro i hi
  rw [vbyte, show 8 * (15 - i) = 8 * (15 - i) from rfl, Mem.extractLsb'_read _ _ (by omega), kb,
    ← hg _ (by omega), ← Mem.readW_byte _ _ (by omega), Offset.add_add, Offset.add_add]
  exact congrArg (fun k => m (S + BitVec.ofNat 64 k)) (by omega)

/-- Storing the four words after the first `K`. -/
theorem store_good {m : Mem} {S : Addr} {f : Nat → BitVec 32} {K : Nat} {v : BitVec 128} (hg : Good m S f K)
    (hv : Rk f K v) (hK : 4 * K + 16 ≤ 240) :
    Good (m.write (S + BitVec.ofNat 64 (4 * K)) 16 v) S f (K + 4) := by
  intro l hl
  by_cases h : l < K
  · rw [Mem.readW, Mem.read_write_sep (Offset.sep S (by omega) (by omega) (by omega)) (by decide)]
    exact hg l h
  · apply VG.Proof.Aes.KeyWords.ext32
    intro q hq
    rw [← Mem.readW_byte _ _ hq, Offset.add_add, Mem.write,
      show S + BitVec.ofNat 64 (4 * l + q) = S + BitVec.ofNat 64 (4 * K) + BitVec.ofNat 64 (4 * (l - K) + q) by
        rw [Offset.add_add]; exact congrArg (fun k => S + BitVec.ofNat 64 k) (by omega),
      Mem.sub_ofNat_toNat _ (by omega), ite_eq_left (by omega)]
    have e := hv (15 - (4 * (l - K) + q)) (by omega)
    rw [vbyte, kb, show 15 - (15 - (4 * (l - K) + q)) = 4 * (l - K) + q by omega,
      show (15 - (4 * (l - K) + q)) / 4 = 3 - (l - K) by omega, show (15 - (4 * (l - K) + q)) % 4 = 3 - q by omega,
      show K + 3 - (3 - (l - K)) = l by omega, show 3 - (3 - q) = q by omega] at e
    exact e

theorem sldoi8_self (x : BitVec 128) : x.extractLsb' 0 64 ++ x.extractLsb' 64 64 = swapDwords x := rfl

end VG.Proof.Aes.PPC64LE.Crypto
