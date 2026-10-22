module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Omega

/-! Shared word arithmetic for the full 64-bit power-of-two metadata. -/

@[expose] public section
namespace VG.Proof.Bignum.TwoPower32

/-- `powStep j`: `y << 2^j` if bit `j` of `x` is set. -/
def pstep (j : Nat) (x y : BitVec 32) : BitVec 32 := y ^^^ (((y <<< (2 ^ j)) ^^^ y) &&& (0 - ((x >>> j) &&& 1)))

/-- The halves of `2^(x mod 64)`, as `powWord` computes them. -/
def pw (x : BitVec 32) : BitVec 32 × BitVec 32 :=
  let x6 := x &&& 63
  let y := pstep 4 x6 (pstep 3 x6 (pstep 2 x6 (pstep 1 x6 (pstep 0 x6 1))))
  let hi := y &&& (0 - ((x6 >>> 5) &&& 1))
  (y ^^^ hi, hi)

theorem and_mask {t k : Nat} (hk : k < 32) :
    BitVec.ofNat 32 t &&& BitVec.ofNat 32 (2 ^ k - 1) = BitVec.ofNat 32 (t % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  have : 2 ^ k ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 ^ k - 1) (by omega),
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
    Nat.mod_eq_of_lt (a := t % 2 ^ k) (by have := Nat.mod_lt t (Nat.two_pow_pos k); omega)]

theorem pw_small : ∀ t < 64, (pw (BitVec.ofNat 32 t)).1.toNat + 2 ^ 32 * (pw (BitVec.ofNat 32 t)).2.toNat = 2 ^ t := by
  decide

theorem pw_mod (t : Nat) : pw (BitVec.ofNat 32 t) = pw (BitVec.ofNat 32 (t % 64)) := by
  have e : ∀ x : Nat, BitVec.ofNat 32 x &&& 63 = BitVec.ofNat 32 (x % 64) := fun x => and_mask (k := 6) (by decide)
  unfold pw
  simp only [e, Nat.mod_mod]

/-- The 64-bit word of the halves is `2^(t mod 64)`. -/
theorem pw_val (t : Nat) :
    (pw (BitVec.ofNat 32 t)).1.toNat + 2 ^ 32 * (pw (BitVec.ofNat 32 t)).2.toNat = 2 ^ (t % 64) := by
  rw [pw_mod]; exact pw_small _ (Nat.mod_lt _ (by decide))

end VG.Proof.Bignum.TwoPower32
