module

public import VerifiedGarbage.Proof.Bignum.TwoPower32

/-! Rotations reuse the shared power-of-two construction's word arithmetic. -/

@[expose] public section
namespace VG.Proof.Bignum.X86.TwoPower

def rotateStep (j : Nat) (x y : BitVec 32) : BitVec 32 :=
  y ^^^ ((y.rotateRight (32 - 2 ^ j) ^^^ y) &&& (0 - ((x >>> j) &&& 1)))

def rotatePower (x : BitVec 32) : BitVec 32 × BitVec 32 :=
  let x6 := x &&& 63
  let y := rotateStep 4 x6 (rotateStep 3 x6 (rotateStep 2 x6 (rotateStep 1 x6 (rotateStep 0 x6 1))))
  let hi := y &&& (0 - ((x6 >>> 5) &&& 1))
  (y ^^^ hi, hi)

private theorem small : ∀ t < 64, rotatePower (BitVec.ofNat 32 t) = TwoPower32.pw (BitVec.ofNat 32 t) := by
  decide

theorem rotate_power_mod (t : Nat) :
    rotatePower (BitVec.ofNat 32 t) = rotatePower (BitVec.ofNat 32 (t % 64)) := by
  have mask : ∀ x : Nat, BitVec.ofNat 32 x &&& 63 = BitVec.ofNat 32 (x % 64) :=
    fun x => TwoPower32.and_mask (t := x) (k := 6) (by decide)
  unfold rotatePower
  simp only [mask, Nat.mod_mod]

theorem rotate_power_eq (t : Nat) : rotatePower (BitVec.ofNat 32 t) = TwoPower32.pw (BitVec.ofNat 32 t) := by
  rw [rotate_power_mod, TwoPower32.pw_mod]
  exact small _ (Nat.mod_lt _ (by decide))

theorem rotate_power_value (t : Nat) :
    (rotatePower (BitVec.ofNat 32 t)).1.toNat + 2 ^ 32 * (rotatePower (BitVec.ofNat 32 t)).2.toNat =
      2 ^ (t % 64) := by
  rw [rotate_power_eq]
  exact TwoPower32.pw_val t

end VG.Proof.Bignum.X86.TwoPower
