module

import VerifiedGarbage.Proof.Rc4.Memory
import VerifiedGarbage.Proof.Rc4.Qword
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Rc4
public import VerifiedGarbage.TCB.Mem

/-!
# RC4: a doubleword scan of the table without compares, step by step

What the 64-bit implementations without compare instructions (RISC-V) hold
after visiting the first doublewords or lanes of a scan of the table
(`gather`, `pick`, `spread`, `scatter`), the masks they make by testing a
value below `2 ^ 63` for zero (`0 - ((v - 1) >> 63)`, `zero_mask`), and facts
about bytes in 64-bit registers, the key offset and the memory around the
context that their proofs share. The algorithm of PPC64LE's proofs
(`Proof/Rc4/PPC64LE/`).
-/

@[expose] public section

namespace VG.Proof.Rc4.Scan64
open VG VG.Spec.Rc4 VG.Proof.Rc4

theorem byte_addr (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-! ## Masks -/

/-- The mask `0 - ((v - 1) >> 63)`. -/
theorem zero_mask (v : BitVec 64) (hv : v.toNat < 2 ^ 63) :
    0#64 - (v - 1#64) >>> 63 = if v = 0#64 then BitVec.allOnes 64 else 0#64 := by
  by_cases h : v = 0#64
  · subst h; decide
  · have hz : (v - 1#64) >>> 63 = 0#64 := by
      have h0 : v.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    rw [hz, ite_eq_right h]; decide

theorem allOnes_and_ite (p : Prop) [Decidable p] (y : BitVec 64) :
    (if p then BitVec.allOnes 64 else 0#64) &&& y = if p then y else 0#64 := by
  split
  · exact BitVec.allOnes_and
  · exact BitVec.zero_and

theorem and_allOnes_ite (p : Prop) [Decidable p] (y : BitVec 64) :
    y &&& (if p then BitVec.allOnes 64 else 0#64) = if p then y else 0#64 := by
  split
  · exact BitVec.and_allOnes
  · exact BitVec.and_zero

/-- The value a row mask tests: zero iff byte `idx` is in doubleword `k`. -/
theorem row_zero (idx : Byte) {k : Nat} (hk : k < 32) :
    (BitVec.ofNat 64 (8 * k) ^^^ idx.setWidth 64) >>> 3 = 0#64 ↔ idx.toNat / 8 = k := by
  rw [← toNat_lt_eight, BitVec.xor_comm]
  exact row_hit idx hk

theorem row_lt (idx : Byte) (k : Nat) :
    ((BitVec.ofNat 64 (8 * k) ^^^ idx.setWidth 64) >>> 3).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := (BitVec.ofNat 64 (8 * k) ^^^ idx.setWidth 64).isLt
  omega

/-- The mask of doubleword `k`: all ones iff it holds byte `idx`. -/
theorem row_mask (idx : Byte) {k : Nat} (hk : k < 32) :
    0#64 - ((BitVec.ofNat 64 (8 * k) ^^^ idx.setWidth 64) >>> 3 - 1#64) >>> 63 =
      if idx.toNat / 8 = k then BitVec.allOnes 64 else 0#64 := by
  rw [zero_mask _ (row_lt idx k)]
  by_cases h : idx.toNat / 8 = k
  · rw [ite_eq_left ((row_zero idx hk).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((row_zero idx hk).mp h')), ite_eq_right h]

theorem low3 (x : BitVec 64) : (x <<< 61) >>> 61 = x &&& BitVec.ofNat 64 7 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_and, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    show (7 % 2 ^ 64 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The value a lane mask tests. -/
theorem lane_val (idx : Byte) {j : Nat} (hj : j < 8) :
    ((BitVec.ofNat 64 j ^^^ idx.setWidth 64) <<< 61) >>> 61 =
      (idx.setWidth 64 &&& BitVec.ofNat 64 7) ^^^ BitVec.ofNat 64 j := by
  rw [low3]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_xor, BitVec.toNat_xor, BitVec.toNat_and,
    Nat.and_xor_distrib_right, Nat.xor_comm]
  congr 1
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (7 % 2 ^ 64 : Nat) = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The mask of lane `j`: all ones iff it is the lane of byte `idx`. -/
theorem lane_mask (idx : Byte) {j : Nat} (hj : j < 8) :
    0#64 - (((BitVec.ofNat 64 j ^^^ idx.setWidth 64) <<< 61) >>> 61 - 1#64) >>> 63 =
      if idx.toNat % 8 = j then BitVec.allOnes 64 else 0#64 := by
  have hz : ∀ x : BitVec 64, x = 0#64 ↔ x.toNat < 1 := by
    intro x; rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]; omega
  have hl : (((BitVec.ofNat 64 j ^^^ idx.setWidth 64) <<< 61) >>> 61).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := ((BitVec.ofNat 64 j ^^^ idx.setWidth 64) <<< 61).isLt
    omega
  rw [zero_mask _ hl, lane_val idx hj]
  by_cases h : idx.toNat % 8 = j
  · rw [ite_eq_left ((hz _).mpr ((lane_hit idx hj).mpr h)), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((lane_hit idx hj).mp ((hz _).mp h'))), ite_eq_right h]

/-! ## The lookup -/

/-- The doubleword holding byte `n`, once doublewords `0, …, k - 1` are visited. -/
def gather (m : Mem) (p : Addr) (n k : Nat) : BitVec 64 :=
  if n / 8 < k then m.readW (p + BitVec.ofNat 64 (8 * (n / 8))) 64 else 0

theorem gather_succ (m : Mem) (p : Addr) (n k : Nat) :
    gather m p n k ||| (if n / 8 = k then m.readW (p + BitVec.ofNat 64 (8 * k)) 64 else 0) =
      gather m p n (k + 1) := by
  unfold gather
  by_cases h0 : n / 8 < k
  · simp [h0, show ¬ n / 8 = k by omega, show n / 8 < k + 1 by omega]
  · by_cases h1 : n / 8 = k
    · subst h1; simp
    · simp [h0, h1, show ¬ n / 8 < k + 1 by omega]

theorem flatMap_succ {α : Type} (f : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The doubleword shifted to byte `L`, once bytes `0, …, j - 1` are visited. -/
def pick (q : BitVec 64) (L j : Nat) : BitVec 64 := if L < j then q >>> (8 * L) else 0

theorem pick_succ (q : BitVec 64) (L j : Nat) :
    pick q L j ||| (if L = j then q >>> (8 * j) else 0) = pick q L (j + 1) := by
  unfold pick
  by_cases h0 : L < j
  · simp [h0, show ¬ L = j by omega, show L < j + 1 by omega]
  · by_cases h1 : L = j
    · subst h1; simp
    · simp [h0, h1, show ¬ L < j + 1 by omega]

theorem low8 (x : BitVec 64) : (x <<< 56) >>> 56 = x &&& BitVec.ofNat 64 255 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_and, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    show (255 % 2 ^ 64 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-! ## The replacement -/

/-- The difference `c`, once lanes `7, …, jj` are visited: shifted to lane `L`
by the lanes visited below it. -/
def spread (c : Byte) (L jj : Nat) : BitVec 64 :=
  if jj ≤ L then (c.setWidth 64) <<< (8 * (L - jj)) else 0#64

/-- A lane visited: the difference shifted up a byte, and added in its lane. -/
theorem spread_succ (c : Byte) (L j : Nat) :
    spread c L (j + 1) <<< 8 ||| (if L = j then c.setWidth 64 else 0#64) = spread c L j := by
  unfold spread
  by_cases h1 : j + 1 ≤ L
  · rw [ite_eq_left h1, ← BitVec.shiftLeft_add, ite_eq_right (show ¬ L = j by omega),
      BitVec.or_zero, ite_eq_left (show j ≤ L by omega), show 8 * (L - (j + 1)) + 8 = 8 * (L - j) by
        omega]
  · rw [ite_eq_right h1, BitVec.zero_shiftLeft, BitVec.zero_or]
    by_cases h2 : L = j
    · rw [ite_eq_left h2, ite_eq_left (show j ≤ L by omega), h2, Nat.sub_self, Nat.mul_zero,
        BitVec.shiftLeft_zero]
    · rw [ite_eq_right h2, ite_eq_right (show ¬ j ≤ L by omega)]

/-- The memory once doublewords `0, …, k - 1` are stored back, XORed with `d`
where they hold byte `n`. -/
def scatter (m : Mem) (p : Addr) (n : Nat) (d : BitVec 64) (k : Nat) : Mem :=
  if n / 8 < k then
    m.writeW (p + BitVec.ofNat 64 (8 * (n / 8)))
      (m.readW (p + BitVec.ofNat 64 (8 * (n / 8))) 64 ^^^ d)
  else m

theorem scatter_succ (m : Mem) (p : Addr) (n : Nat) (d : BitVec 64) (k : Nat) :
    (scatter m p n d k).writeW (p + BitVec.ofNat 64 (8 * k))
      ((scatter m p n d k).readW (p + BitVec.ofNat 64 (8 * k)) 64 ^^^
        (if n / 8 = k then d else 0#64)) = scatter m p n d (k + 1) := by
  unfold scatter
  by_cases h0 : n / 8 < k
  · rw [ite_eq_left h0, ite_eq_right (show ¬ n / 8 = k by omega), BitVec.xor_zero, writeW_readW,
      ite_eq_left (show n / 8 < k + 1 by omega)]
  · rw [ite_eq_right h0]
    by_cases h1 : n / 8 = k
    · rw [ite_eq_left h1, ite_eq_left (show n / 8 < k + 1 by omega), h1]
    · rw [ite_eq_right h1, BitVec.xor_zero, writeW_readW,
        ite_eq_right (show ¬ n / 8 < k + 1 by omega)]

theorem xor_byte (a b : Byte) : a.setWidth 64 ^^^ b.setWidth 64 = (a ^^^ b).setWidth 64 := by
  rw [BitVec.setWidth_xor]

/-! ## Bytes in registers -/

theorem low_byte (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem ofNat_low (r : Nat) : (BitVec.ofNat 64 r).setWidth 8 = BitVec.ofNat 8 r := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem mask255 (x : BitVec 64) : (x <<< 56) >>> 56 = (x.setWidth 8).setWidth 64 := by
  rw [low8]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (255 % 2 ^ 64 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem byte_add (a b : Byte) :
    ((a.setWidth 64 + b.setWidth 64) <<< 56) >>> 56 = (a + b).setWidth 64 := by
  rw [mask255]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega

theorem byte_add3 (j a k : Byte) :
    ((j.setWidth 64 + a.setWidth 64 + k.setWidth 64) <<< 56) >>> 56 = (j + a + k).setWidth 64 := by
  rw [mask255]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega

theorem byte_inc (i : Byte) :
    ((i.setWidth 64 + 1#64) <<< 56) >>> 56 = (i + 1#8).setWidth 64 := by
  have h := byte_add i 1#8
  rwa [show (1#8).setWidth 64 = 1#64 from rfl] at h

theorem low_xor (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 = a ^^^ b := by
  rw [xor_byte, low_byte]

/-! ## Counters -/

theorem sub256_ne (j : Nat) (hj : j + 1 < 256) :
    (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 256 == (0 : BitVec 64)) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro h
  have hh := congrArg BitVec.toNat h
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hh
  change _ = 0 at hh
  omega

theorem len_ne (n : Nat) (hn : n + 1 + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 (n + 1 + 1) - 1#64 == (0 : BitVec 64)) = false := by
  apply beq_eq_false_iff_ne.mpr
  rw [Offset.ofNat_sub_ofNat (by omega)]
  intro hz0
  have hh := congrArg BitVec.toNat hz0
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hh
  change n + 1 + 1 - 1 = 0 at hh
  omega

theorem valid_length (len : BitVec 64) :
    (len - 1#64) >>> 8 = (0 : BitVec 64) ↔ 1 ≤ len.toNat ∧ len.toNat ≤ 256 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl]
  omega

/-! ## The key offset -/

/-- The key offset after `o`, advanced to `o + 1` and back to 0 at the key
length `len`, without a branch. -/
def offNext (o len : BitVec 64) : BitVec 64 :=
  (o + 1#64) &&& (((o + 1#64 - len - 1#64) ^^^ (o + 1#64 - len)) >>> 63 - 1#64)

theorem offNext_eq (r : Nat) (len : BitVec 64) (hl : 0 < len.toNat) (hlen : len.toNat ≤ 256) :
    offNext (BitVec.ofNat 64 (r % len.toNat)) len = BitVec.ofNat 64 ((r + 1) % len.toNat) := by
  have hb := Nat.mod_lt r hl
  have ht : (BitVec.ofNat 64 (r % len.toNat) + 1#64).toNat = r % len.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show r % len.toNat < 2 ^ 64 by omega)]
    change (r % len.toNat + 1) % 2 ^ 64 = _
    omega
  have ha : (r + 1) % len.toNat = (r % len.toNat + 1) % len.toNat := by
    simp only [Nat.add_mod, Nat.mod_mod]
  unfold offNext
  by_cases h : r % len.toNat + 1 < len.toNat
  · have hd : ∀ x : BitVec 64, x.toNat = 2 ^ 64 - (len.toNat - (r % len.toNat + 1)) →
        x >>> 63 = 1#64 := by
      intro x hx
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hx]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    have h1 : (BitVec.ofNat 64 (r % len.toNat) + 1#64 - len) >>> 63 = 1#64 :=
      hd _ (by rw [BitVec.toNat_sub, ht]; omega)
    have h2 : (BitVec.ofNat 64 (r % len.toNat) + 1#64 - len - 1#64) >>> 63 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_sub, ht]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    rw [BitVec.ushiftRight_xor_distrib, h1, h2, show (1#64 ^^^ 1#64) - 1#64 = BitVec.allOnes 64 by
      decide, BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    rw [ht, BitVec.toNat_ofNat, ha, Nat.mod_eq_of_lt h,
      Nat.mod_eq_of_lt (show r % len.toNat + 1 < 2 ^ 64 by omega)]
  · have he : BitVec.ofNat 64 (r % len.toNat) + 1#64 = len := by
      apply BitVec.eq_of_toNat_eq
      rw [ht]; omega
    rw [he, BitVec.sub_self, ha, show r % len.toNat + 1 = len.toNat by omega, Nat.mod_self,
      show (0#64 - 1#64 ^^^ 0#64) >>> 63 - 1#64 = 0#64 by decide, BitVec.and_zero]

end VG.Proof.Rc4.Scan64
