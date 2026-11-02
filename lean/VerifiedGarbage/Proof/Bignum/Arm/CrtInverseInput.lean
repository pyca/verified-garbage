module
public import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandState
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Impl.Bignum.Arm.CrtDifference
import VerifiedGarbage.Impl.Bignum.Arm.R2


/-! # The secret CRT inverse is read from the original private-key bytes -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.Rsa.Mont (numAt)

structure CrtInverseInput (base src : BitVec 32) (len w k M : Nat) (bs : List Byte) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  modulus : numAt s.mem (State.addr base) w 0 = M
  odd : M % 2 = 1
  r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M
  source : SavedOperand base src len k 96 100 bs s
  positive : 0 < k
  fits : k ≤ 8 * w

end VG.Proof.Bignum.Arm
