import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Select32`. -/
section

/-! # Arithmetic selection lemmas for RC2's constant-time lookups -/

namespace VG.Proof.Rc2.Word32

theorem maskByte (x : BitVec 32) : x &&& 255 = (x.setWidth 8).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change x.toNat &&& (2 ^ 8 - 1) = x.toNat % 256 % 4294967296
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem joinBytes (lo hi : Byte) :
    lo.setWidth 32 ||| (hi.setWidth 32).rotateRight 24 =
      (lo.setWidth 16 ||| hi.setWidth 16 <<< 8).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_shiftLeft]
  by_cases h8 : j < 8
  · simp (disch := omega) [h8, show j < 16 by omega,
      BitVec.getLsbD_of_ge]
  · by_cases h16 : j < 16
    · simp (disch := omega) [h8, h16, hj, show j - 8 < 32 by omega,
        show j - 8 < 16 by omega, BitVec.getLsbD_of_ge]
    · simp (disch := omega) [h8, h16,
        BitVec.getLsbD_of_ge]

/-- Subtraction exposes zero in the top bit for inputs smaller than 2³¹. -/
theorem zeroBit (x : BitVec 32) (hx : x.toNat < 2 ^ 31) :
    (x - 1) >>> 31 = if x = 0 then 1 else 0 := by
  by_cases h : x = 0
  · subst x; decide
  · simp only [h, ite_false]
    bv_omega

theorem selectMask_eq (x y : BitVec 8) :
    (0 - (((x.setWidth 32 ^^^ y.setWidth 32) - 1) >>> 31) : BitVec 32) =
      if x = y then BitVec.allOnes 32 else 0 := by
  have hbound : (x.setWidth 32 ^^^ y.setWidth 32).toNat < 2 ^ 31 := by
    rw [← BitVec.setWidth_xor]
    simp only [BitVec.toNat_setWidth]
    have := (x ^^^ y).isLt
    omega
  rw [VG.Proof.Rc2.Word32.zeroBit _ hbound]
  have he : (x.setWidth 32 ^^^ y.setWidth 32 = 0#32) ↔ x = y := by
    rw [BitVec.xor_eq_zero_iff]
    constructor
    · intro h
      have := congrArg (BitVec.setWidth 8) h
      simpa using this
    · exact congrArg (BitVec.setWidth 32)
  by_cases h : x = y
  · subst y; simp
  · have hn := mt he.mp h
    simp [hn, h]

/-- OR accumulation of a uniquely selected candidate, even in an arbitrary
order. Repeated candidates are harmless because OR is idempotent. -/
theorem select_fold (f : Nat → BitVec 32) (x : Nat) (is : List Nat) (acc : BitVec 32) :
    is.foldl (fun a i => a ||| if x = i then f i else 0) acc =
      acc ||| if x ∈ is then f x else 0 := by
  induction is generalizing acc with
  | nil => simp
  | cons i is ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    by_cases h : x = i
    · subst i
      by_cases hm : x ∈ is <;> simp [hm, BitVec.or_assoc]
    · by_cases hm : x ∈ is <;> simp [h, hm]

end VG.Proof.Rc2.Word32

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Word32`. -/
section

/-! # RC2 word arithmetic in 32-bit registers -/

namespace VG.Proof.Rc2.Word32

theorem maskWord (x : BitVec 32) : x &&& 65535 = (x.setWidth 16).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change x.toNat &&& (2 ^ 16 - 1) = x.toNat % 65536 % 4294967296
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem maskWord_lit (x : BitVec 32) : x &&& 65535#32 = (x.setWidth 16).setWidth 32 :=
  VG.Proof.Rc2.Word32.maskWord x

theorem rotateWord (x : BitVec 16) (n : Nat) (hn : 1 ≤ n) (hn' : n < 16) :
    ((x.setWidth 32).rotateRight (32 - n) ||| (x.setWidth 32) >>> (16 - n)) &&& 65535 =
      (x.rotateLeft n).setWidth 32 := by
  rw [VG.Proof.Rc2.Word32.maskWord]
  apply congrArg (BitVec.setWidth 32)
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateLeft]
  have n32 : (32 - n) % 32 = 32 - n := Nat.mod_eq_of_lt (by omega)
  have n16 : n % 16 = n := Nat.mod_eq_of_lt hn'
  rw [n32, n16]
  rw [show 32 - (32 - n) = n by omega]
  by_cases h : j < n
  · simp (disch := omega) [h, hj,
      show j + (16 - n) < 32 by omega, BitVec.getLsbD_of_ge, Nat.add_comm]
  · simp (disch := omega) [h, hj, show j < 32 by omega,
      show j - n < 32 by omega, BitVec.getLsbD_of_ge]

theorem mixWord (x k a b c : BitVec 16) :
    (x.setWidth 32 + k.setWidth 32 +
      ((a.setWidth 32 &&& b.setWidth 32) + (~~~(a.setWidth 32) &&& c.setWidth 32))) &&& 65535 =
      (x + k + (a &&& b) + (~~~a &&& c)).setWidth 32 := by
  rw [VG.Proof.Rc2.Word32.maskWord]
  apply congrArg (BitVec.setWidth 32)
  simp [BitVec.setWidth_add, BitVec.setWidth_not, BitVec.add_assoc]

theorem reverseMixWord (x k a b c : BitVec 16) :
    (x.setWidth 32 - k.setWidth 32 -
      ((a.setWidth 32 &&& b.setWidth 32) + (~~~(a.setWidth 32) &&& c.setWidth 32))) &&& 65535 =
      (x - k - (a &&& b) - (~~~a &&& c)).setWidth 32 := by
  rw [VG.Proof.Rc2.Word32.maskWord]
  apply congrArg (BitVec.setWidth 32)
  simp [BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le,
    BitVec.setWidth_not, BitVec.add_assoc, BitVec.neg_add]

theorem rotateLeft_reverse (x : BitVec 16) (n : Nat) (hn : 1 ≤ n) (hn' : n < 16) :
    x.rotateLeft (16 - n) = x.rotateRight n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight,
    Nat.mod_eq_of_lt hn', Nat.mod_eq_of_lt (show 16 - n < 16 by omega),
    show 16 - (16 - n) = n by omega]

theorem subInputsWord (x k c : BitVec 32) :
    (x - k - c) &&& 65535 =
      (x.setWidth 16 - k.setWidth 16 - c.setWidth 16).setWidth 32 := by
  rw [VG.Proof.Rc2.Word32.maskWord]
  simp [BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le]

theorem joinBytes_shift (lo hi : VG.Byte) :
    lo.setWidth 32 ||| hi.setWidth 32 <<< 8 =
      (lo.setWidth 16 ||| hi.setWidth 16 <<< 8).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft]
  by_cases h : j < 16
  · simp (disch := omega) [h, hj, show j - 8 < 32 by omega, show j - 8 < 16 by omega]
  · simp (disch := omega) [h, hj, BitVec.getLsbD_of_ge]

end VG.Proof.Rc2.Word32

end
