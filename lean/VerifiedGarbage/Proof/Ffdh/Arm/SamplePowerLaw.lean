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
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerAt

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

structure SamplePowerLaw (code : Prog isa) : Prop where
  correct : ∀ (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {eb : List Byte},
    SampleContext p l slots s → KeyCallMemory p s → stableSlots slots = true →
    56 ∈ slots → 32 ∈ slots →
    ArithmeticReady p.base p.len p.w s →
    numAt s.mem (State.addr p.base) p.w 0 = p.P → p.P % 2 = 1 →
    numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P →
    Octets p.base l.start p.len eb s → eb.length = l.width →
    WP isa code s fun t => Context p slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 6 = Spec.Rsa.powMod p.G (Spec.Rsa.os2ip eb) p.P ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      numAt t.mem (State.addr p.base) p.w 7 = 1 ∧
      Frame [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t
  ct : ∀ {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {eb1 eb2 : List Byte},
    stableSlots slots = true → 56 ∈ slots → 32 ∈ slots →
    eb1.length = l.width → eb2.length = l.width → p.P % 2 = 1 →
    RelCT isa (fun s t => (SamplePowerInput p l slots eb1 s ∧ KeyCallMemory p s) ∧
      (SamplePowerInput p l slots eb2 t ∧ KeyCallMemory p t) ∧ s.sp = t.sp) code (fun _ _ => True)

end VG.Proof.Ffdh.Arm
