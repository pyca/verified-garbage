module

public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout

/-! # The shared key-generation exponentiator's caller contract -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure SamplePowerInput (p : Inputs) (l : ScalarLayout p) (slots : List Nat)
    (eb : List Byte) (s : State) : Prop where
  context : SampleContext p l slots s
  ready : ArithmeticReady p.base p.len p.w s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P
  r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P
  exponent : Octets p.base l.start p.len eb s
  outputs : KeyOutputs p s

end VG.Proof.Ffdh.Arm
