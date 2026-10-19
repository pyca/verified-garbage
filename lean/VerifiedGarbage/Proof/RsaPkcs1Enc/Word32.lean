module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Select
public import VerifiedGarbage.Proof.Framework.Omega

/-! # Word arithmetic for branchless implicit rejection -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.Word32
open VG
open VG.Proof.RsaPkcs1Enc (vOf firstZero)

theorem top_sub {k x : Nat} (hk : k < 2 ^ 31) (hx : x < 2 ^ 31) :
    (BitVec.ofNat 32 k - BitVec.ofNat 32 x) >>> 31 = if k < x then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := x) (by omega)]
  by_cases h : k < x
  · simp only [h, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (by omega)]
    show _ = 1
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · simp only [h, ↓reduceIte]
    rw [show 2 ^ 32 - x + k = (k - x) + 2 ^ 32 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    show _ = 0
    exact Nat.div_eq_of_lt (by omega)

theorem isZero_bit (x : BitVec 32) (hx : x.toNat < 2 ^ 31) : (x - 1) >>> 31 = if x = 0 then 1 else 0 := by
  by_cases h : x = 0
  · subst h; decide
  · have h0 : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    simp only [h, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub,
      show (1 : BitVec 32).toNat = 1 from rfl]
    show _ = 0
    omega

theorem byte_lt (b : Byte) : (b.setWidth 32).toNat < 2 ^ 31 := by
  have := b.isLt; simp only [BitVec.toNat_setWidth]; omega

theorem setWidth_ne_zero {b : Byte} (h : b ≠ 0) : b.setWidth 32 ≠ 0 := by
  intro e
  have := congrArg (BitVec.setWidth 8) e
  simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq] at this
  exact h (this.trans rfl)

theorem zbit (b : Byte) :
    (if b.setWidth 32 = 0 then (1 : BitVec 32) else 0) = BitVec.ofNat 32 (decide (b = 0)).toNat := by
  by_cases h : b = 0
  · subst h; rfl
  · simp only [setWidth_ne_zero h, ↓reduceIte, h, decide_false]; rfl

theorem bit_toNat (p : Bool) : (if p = true then (1 : BitVec 32) else 0) = BitVec.ofNat 32 p.toNat := by
  cases p <;> rfl

theorem negbit (b : Bool) : (0 : BitVec 32) - BitVec.ofNat 32 b.toNat = if b then BitVec.allOnes 32 else 0 := by
  cases b <;> decide

theorem sel2 (x y : BitVec 32) (b : Bool) :
    ((x ^^^ y) &&& (if b then BitVec.allOnes 32 else 0)) ^^^ y = if b then x else y := by
  cases b
  · simp
  · show ((x ^^^ y) &&& BitVec.allOnes 32) ^^^ y = x
    rw [BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem band (a b : Bool) : BitVec.ofNat 32 a.toNat &&& BitVec.ofNat 32 b.toNat = BitVec.ofNat 32 (a && b).toNat := by
  cases a <;> cases b <;> decide

theorem mask_and (v : Nat) (b : Bool) :
    BitVec.ofNat 32 v &&& (if b then BitVec.allOnes 32 else 0) = BitVec.ofNat 32 (if b then v else 0) := by
  cases b
  · simp
  · exact BitVec.and_allOnes

theorem ge10 {sep : Nat} :
    ((if sep < 10 then (1 : BitVec 32) else 0) ^^^ 1) = BitVec.ofNat 32 (decide (10 ≤ sep)).toNat := by
  by_cases h : sep < 10
  · simp only [h, ↓reduceIte, show ¬ 10 ≤ sep by omega, decide_false]; decide
  · simp only [h, ↓reduceIte, show 10 ≤ sep by omega, decide_true]; decide

theorem xbit (b : Byte) :
    (if b.setWidth 32 ^^^ 2 = 0 then (1 : BitVec 32) else 0) = BitVec.ofNat 32 (decide (b = 2)).toNat := by
  by_cases h : b = 2
  · subst h; decide
  · have : b.setWidth 32 ^^^ 2 ≠ 0 := by
      intro e
      have e1 := congrArg (· ^^^ (2 : BitVec 32)) e
      simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at e1
      have e2 := congrArg (BitVec.setWidth 8) e1
      simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq] at e2
      exact h (e2.trans (by decide))
    simp only [this, ↓reduceIte, h, decide_false]; rfl

theorem xor2_lt (b : Byte) : (b.setWidth 32 ^^^ 2).toNat < 2 ^ 31 := by
  have := b.isLt
  rw [BitVec.toNat_xor, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have := Nat.xor_lt_two_pow (n := 8) (x := b.toNat) (y := (2 : BitVec 32).toNat) (by omega) (by decide)
  omega

theorem vOf_bits (b0 b1 : Byte) (f : Bool) (sep : Nat) :
    (((decide (b0 = 0) && decide (b1 = 2)) && f) && decide (10 ≤ sep)) = vOf b0 b1 f sep := by
  simp only [vOf, Bool.decide_and, Bool.decide_eq_true, Bool.and_assoc]

theorem selByte (e a : Byte) (v : Bool) (c : Prop) [Decidable c] :
    ((if v then e.setWidth 32 else a.setWidth 32) &&& (if c then BitVec.allOnes 32 else 0)).setWidth 8 =
      if c then (if v then e else a) else 0 := by
  (by_cases h : c <;> cases v <;> simp [h]) <;> exact BitVec.and_allOnes

theorem mask_ge {j kl : Nat} (hj : j < 2 ^ 31) (hk : kl < 2 ^ 31) (c : Bool) :
    ((BitVec.ofNat 32 j - BitVec.ofNat 32 kl) >>> 31 - 1) &&& (if c then BitVec.allOnes 32 else 0) =
      if kl ≤ j ∧ c = true then BitVec.allOnes 32 else 0 := by
  rw [top_sub hj hk]
  by_cases h : j < kl
  · simp only [h, ↓reduceIte, show ¬ (kl ≤ j ∧ c = true) from fun h' => by omega]
    cases c <;> decide
  · simp only [h, ↓reduceIte, show kl ≤ j by omega, true_and]
    cases c <;> decide

theorem negate_eq (x : BitVec 32) : (x ^^^ BitVec.allOnes 32) + 1 = -x := by
  rw [BitVec.xor_allOnes, show (1 : BitVec 32) = 1#32 from rfl, ← BitVec.neg_eq_not_add]

theorem scan_step (EM : List Byte) {i : Nat} (hi : 2 ≤ i) :
    (BitVec.ofNat 32 ((firstZero EM i).getD 0) ||| ((-((BitVec.ofNat 32 (firstZero EM i).isSome.toNat ^^^ 1) &&&
      BitVec.ofNat 32 (decide (EM.getD i 1 = 0)).toNat)) &&& BitVec.ofNat 32 i) =
        BitVec.ofNat 32 ((firstZero EM (i + 1)).getD 0)) ∧
    ((BitVec.ofNat 32 (firstZero EM i).isSome.toNat ||| BitVec.ofNat 32 (decide (EM.getD i 1 = 0)).toNat) =
      BitVec.ofNat 32 (firstZero EM (i + 1)).isSome.toNat) := by
  rw [firstZero]
  cases hf : firstZero EM i with
  | some k =>
    simp only [Option.isSome_some, Option.getD_some, Bool.toNat_true]
    cases decide (EM.getD i 1 = 0) <;> simp
  | none =>
    simp only [Option.isSome_none, Option.getD_none, Bool.toNat_false]
    by_cases e : EM.getD i 1 = 0
    · rw [decide_eq_true e]
      simp only [e, hi, and_self, ↓reduceIte, Option.getD_some, Option.isSome_some,
        Bool.toNat_true]
      refine ⟨?_, by decide⟩
      rw [show -((BitVec.ofNat 32 0 ^^^ 1) &&& BitVec.ofNat 32 1) = BitVec.allOnes 32 by decide,
        BitVec.allOnes_and]
      exact BitVec.zero_or
    · rw [decide_eq_false e]
      simp only [e, and_false, ↓reduceIte, Option.getD_none, Option.isSome_none, Bool.toNat_false]
      refine ⟨?_, by decide⟩
      rw [show -((BitVec.ofNat 32 0 ^^^ 1) &&& BitVec.ofNat 32 0) = 0 by decide]
      simp

theorem count_eq {n : Nat} (bound : n < 2 ^ 32) :
    (0 : BitVec 32) ++ BitVec.ofNat 32 n = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound,
    Nat.mod_eq_of_lt (by omega)]
  simp

theorem sub_beq_zero {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have nonzero : BitVec.ofNat 32 a - BitVec.ofNat 32 b ≠ 0 := by
      intro e
      have eq := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at eq
      change (2 ^ 32 - b + a) % 2 ^ 32 = 0 at eq
      omega
    rw [beq_eq_false_iff_ne.mpr nonzero, decide_eq_false h]

end VG.Proof.RsaPkcs1Enc.Word32
