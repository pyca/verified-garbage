module

public import VerifiedGarbage.Proof.MillerRabin.Word32

/-! # Folding the exponent marker derives the final secret square threshold -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86

private theorem double_eq_shift (x : BitVec 32) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

def markerFold (lo hi : BitVec 32) : BitVec 32 :=
  let x1 := lo ||| hi
  let x2 := x1 ||| x1 >>> 16
  let x3 := x2 ||| x2 >>> 8
  let x4 := x3 ||| x3 >>> 4
  let b1 := x4 >>> 1 &&& 1
  let b2 := x4 >>> 2 &&& 1
  let b3 := x4 >>> 3 &&& 1
  b3 + b1 + b1 + b1 + b2 + b2

theorem markerFold_eq (lo hi : BitVec 32) : markerFold lo hi = Word32.foldR lo hi := by
  unfold markerFold Word32.foldR
  dsimp only
  rw [← double_eq_shift, ← double_eq_shift]
  simp only [BitVec.add_assoc]
  rfl

theorem markerFold_twoPow {k : Nat} (bound : k < 64) :
    markerFold (BitVec.ofNat 32 (2 ^ k % 2 ^ 32)) (BitVec.ofNat 32 (2 ^ k / 2 ^ 32)) =
      BitVec.ofNat 32 (4 - VG.Proof.RsaKeyGen.sigOf k) := by
  rw [markerFold_eq]
  exact Word32.foldR_eq k bound

end VG.Proof.MillerRabin.X86
