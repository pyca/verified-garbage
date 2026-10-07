import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Impl.P256.VerifySparse

namespace VG.Proof.P256.VerifySparse
open VG VG.AArch64 VG.Proof.Ed25519

def p : Nat := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

def four (a b c d : BitVec 64) : Nat :=
  a.toNat+2^64*(b.toNat+2^64*(c.toNat+2^64*d.toNat))

/-- Sparse correction words synthesized from a zero/all-ones mask. -/
theorem masked_words (b : Bool) :
    let m : BitVec 64 := if b then -1 else 0
    m >>> 32 = (if b then 0xffffffff else 0) ∧
    (m <<< 32)-m = (if b then 0xffffffff00000001 else 0) ∧
    four m (m >>> 32) 0 ((m <<< 32)-m) = if b then p else 0 := by
  cases b <;> decide

/-- Four-word addition modulo its radix, independent of the final carry flag. -/
theorem addFour_value (a b c d x y z w : BitVec 64) :
    let u := Word64.addCarry a x false
    let c0 := Word64.carryOut a x false
    let v := Word64.addCarry b y c0
    let c1 := Word64.carryOut b y c0
    let r := Word64.addCarry c z c1
    let c2 := Word64.carryOut c z c1
    let t := Word64.addCarry d w c2
    four u v r t = (four a b c d+four x y z w)%2^256 := by
  dsimp only
  have h0 := Word64.addCarry_value a x false
  have h1 := Word64.addCarry_value b y (Word64.carryOut a x false)
  have h2 := Word64.addCarry_value c z (Word64.carryOut b y (Word64.carryOut a x false))
  have h3 := Word64.addCarry_value d w (Word64.carryOut c z (Word64.carryOut b y (Word64.carryOut a x false)))
  have l0 := (Word64.addCarry a x false).isLt
  have l1 := (Word64.addCarry b y (Word64.carryOut a x false)).isLt
  have l2 := (Word64.addCarry c z (Word64.carryOut b y (Word64.carryOut a x false))).isLt
  have l3 := (Word64.addCarry d w (Word64.carryOut c z (Word64.carryOut b y (Word64.carryOut a x false)))).isLt
  simp only [Bool.toNat_false,Nat.add_zero] at h0
  unfold four
  omega

end VG.Proof.P256.VerifySparse
