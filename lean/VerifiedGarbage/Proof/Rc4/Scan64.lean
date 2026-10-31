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
after visiting the first doublewords of a scan of the table (`gather`,
`scatter`), and facts about masks, bytes in 64-bit registers, the key
offset and the memory around the context that their proofs share.
-/

@[expose] public section

namespace VG.Proof.Rc4.Scan64
open VG VG.Spec.Rc4 VG.Proof.Rc4

theorem byte_addr (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-! ## Masks -/

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

/-! ## The replacement -/

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

theorem low8 (x : BitVec 64) : (x <<< 56) >>> 56 = x &&& BitVec.ofNat 64 255 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_and, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    show (255 % 2 ^ 64 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
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
