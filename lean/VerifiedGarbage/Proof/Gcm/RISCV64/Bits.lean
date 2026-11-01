module

public import VerifiedGarbage.Proof.Gcm.Spec

/-!
# GHASH on RISC-V: blocks as two words

Untrusted: everything here is checked by Lean. A block as its high and low
64-bit words (`w2`), and what the instructions of `Impl/Gcm/RISCV64.lean`
compute on them, stated on whole blocks: the step of Algorithm 1's `V`
(`vstep`, `tab_step`), the masks (`mask_shl`), a masked accumulation
(`acc_mask`) and the shift of `x` by a byte (`w2_shl8`). The values of `V`
do not depend on the factor `x` (`mulSteps_snd`), so a table of them serves
every block.
-/

@[expose] public section

namespace VG.Proof.Gcm.RISCV64

open VG.Spec.Gcm (Block R mul)
open VG.Proof.Gcm

/-! ## Algorithm 1 with the values of `V` given -/

/-- Algorithm 1's step of `V`. -/
def vstep (v : Block) : Block := if v.getLsbD 0 then (v >>> 1) ^^^ R else v >>> 1

/-- `Vᵢ`, from `V₀ = H`. -/
def vs (h : Block) : Nat → Block
  | 0 => h
  | i + 1 => vstep (vs h i)

theorem mulSteps_snd (x h : Block) : ∀ i, (mulSteps x h i).2 = vs h i
  | 0 => rfl
  | i + 1 => by rw [mulSteps_succ, mulStep, mulSteps_snd x h i]; rfl

theorem mulSteps_fst_succ (x h : Block) (i : Nat) :
    (mulSteps x h (i + 1)).1 =
      if x.getMsbD i then (mulSteps x h i).1 ^^^ vs h i else (mulSteps x h i).1 := by
  rw [mulSteps_succ, mulStep, mulSteps_snd]

/-! ## Two words -/

/-- The block of the high word `a` and the low word `b`. -/
abbrev w2 (a b : BitVec 64) : Block := a ++ b

theorem getLsbD_w2 (a b : BitVec 64) (i : Nat) :
    (w2 a b).getLsbD i = if i < 64 then b.getLsbD i else a.getLsbD (i - 64) := by
  simp only [w2, BitVec.getLsbD_append]

theorem w2_xor (a b c d : BitVec 64) : w2 a b ^^^ w2 c d = w2 (a ^^^ c) (b ^^^ d) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_xor, getLsbD_w2, getLsbD_w2, getLsbD_w2]
  split <;> simp [BitVec.getLsbD_xor]

theorem w2_zero : w2 0 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_w2]; split <;> simp

/-- The high word's bits, from the left, are the block's first 64. -/
theorem getMsbD_w2 (a b : BitVec 64) {k : Nat} (hk : k < 64) : (w2 a b).getMsbD k = a.getMsbD k := by
  rw [BitVec.getMsbD_eq_getLsbD, BitVec.getMsbD_eq_getLsbD, getLsbD_w2]
  simp only [show k < 64 + 64 by omega, hk, decide_true, Bool.true_and]
  rw [ite_eq_right (show ¬ 128 - 1 - k < 64 by omega)]
  congr 1
  omega

/-! ## Masks -/

/-- `0` or all ones. -/
abbrev mask (c : Bool) : BitVec 64 := if c then BitVec.allOnes 64 else 0

/-- `srai 63` of `x << k` is all ones exactly when bit `k` (from the left) of `x` is set. -/
theorem mask_shl (x : BitVec 64) {k : Nat} (hk : k < 64) :
    (x <<< k).sshiftRight 63 = mask (x.getMsbD k) := by
  have hm : (x <<< k).msb = x.getMsbD k := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft, BitVec.getMsbD_eq_getLsbD]
    simp [hk, show ¬ 64 - 1 < k by omega]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight]
  simp only [show ¬ 64 ≤ i by omega, decide_false, Bool.not_false, Bool.true_and]
  have he : (if 63 + i < 64 then (x <<< k).getLsbD (63 + i) else (x <<< k).msb) = (x <<< k).msb := by
    split
    · rw [show 63 + i = 64 - 1 by omega, BitVec.msb_eq_getLsbD_last]
    · rfl
  rw [he, hm]
  cases x.getMsbD k
  · simp [mask]
  · simp only [mask, ite_true, BitVec.getLsbD_allOnes, hi, decide_true]

/-- `srai 63` of `x << 63` is all ones exactly when the lowest bit of `x` is set. -/
theorem mask_lsb (x : BitVec 64) : (x <<< 63).sshiftRight 63 = mask (x.getLsbD 0) := by
  rw [mask_shl x (by decide), BitVec.getMsbD_eq_getLsbD]; rfl

/-- `Z := Z ⊕ (U ∧ M)`, word by word, for the mask of `c`. -/
theorem acc_mask (z0 z1 u0 u1 : BitVec 64) (c : Bool) :
    w2 (z0 ^^^ (u0 &&& mask c)) (z1 ^^^ (u1 &&& mask c)) = if c then w2 z0 z1 ^^^ w2 u0 u1 else w2 z0 z1 := by
  cases c
  · simp [mask]
  · simp only [mask, ite_true, BitVec.and_allOnes, w2_xor]

/-! ## The step of `V` -/

/-- `R`'s high word, as the code builds it (`li -31`, `slli 56`). -/
theorem rr_eq : BitVec.ofInt 64 (-31) <<< 56 = 0xE100000000000000#64 := by decide

theorem R_w2 : R = w2 0xE100000000000000#64 0 := by decide

/-- The shifts and `or` shift the two words right by one bit. -/
theorem w2_shr1 (a b : BitVec 64) : w2 (a >>> 1) (b >>> 1 ||| a <<< 63) = w2 a b >>> 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, getLsbD_w2, getLsbD_w2]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  rcases (by omega : i < 63 ∨ i = 63 ∨ (64 ≤ i ∧ i < 127) ∨ i = 127) with h | h | h | h
  · simp [h, show i < 64 by omega, show 1 + i < 64 by omega]
  · subst h; simp
  · simp [show ¬ i < 64 by omega, show ¬ 1 + i < 64 by omega, show 1 + (i - 64) = 1 + i - 64 by omega]
  · subst h; simp

/-- `tabStep`'s computation of the next `V`. -/
theorem tab_step (a b : BitVec 64) :
    w2 (a >>> 1 ^^^ ((b <<< 63).sshiftRight 63 &&& BitVec.ofInt 64 (-31) <<< 56)) (b >>> 1 ||| a <<< 63) =
      vstep (w2 a b) := by
  have h0 : (w2 a b).getLsbD 0 = b.getLsbD 0 := by rw [getLsbD_w2]; rfl
  rw [vstep, h0, ← w2_shr1, mask_lsb, rr_eq, R_w2]
  cases b.getLsbD 0
  · simp [mask]
  · simp only [mask, ite_true, BitVec.allOnes_and, w2_xor]; simp

/-! ## The shift of `x` -/

theorem w2_shl8 (a b : BitVec 64) : w2 (a <<< 8 ||| b >>> 56) (b <<< 8) = w2 a b <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_shiftLeft, getLsbD_w2, getLsbD_w2]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 72) ∨ 72 ≤ i) with h | h | h | h
  · simp [h, show i < 64 by omega]
  · simp [show i < 64 by omega, show ¬ i < 8 by omega, hi, show i - 8 < 64 by omega]
  · simp [show ¬ i < 64 by omega, show i - 64 < 8 by omega, show ¬ i < 8 by omega, hi,
      show 56 + (i - 64) = i - 8 by omega, show i - 8 < 64 by omega]
  · simp [show ¬ i < 64 by omega, show ¬ i - 64 < 8 by omega, show ¬ i < 8 by omega, hi,
      show i - 64 - 8 = i - 8 - 64 by omega, show ¬ i - 8 < 64 by omega, show i - 64 < 64 by omega,
      BitVec.getLsbD_of_ge b (56 + (i - 64)) (by omega)]

/-- Bit `k` of the top byte of `x <<< 8j` is bit `8j + k` of `x`. -/
theorem getMsbD_shl8 (x : Block) (j k : Nat) :
    (x <<< (8 * j)).getMsbD k = x.getMsbD (8 * j + k) := by
  rw [BitVec.getMsbD_shiftLeft]
  simp [Nat.add_comm]

end VG.Proof.Gcm.RISCV64
