module

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerAt

/-! # The shared key-generation exponentiator's caller contract -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure KeyPowerLaw (code : Prog isa) : Prop where
  correct : ∀ (s : State) {p : Inputs} {slots : List Nat} {eb : List Byte},
    Context p slots s → KeyCallMemory p s → stableSlots slots = true →
    56 ∈ slots → 16 ∈ slots → 20 ∈ slots → 32 ∈ slots →
    ArithmeticReady p.base p.len p.w s →
    numAt s.mem (State.addr p.base) p.w 0 = p.P → p.P % 2 = 1 →
    numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P →
    Octets p.base p.scalarStart p.len eb s → eb.length = p.scalarWidth →
    WP isa code s fun t => Context p slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 6 = Spec.Rsa.powMod p.G (Spec.Rsa.os2ip eb) p.P ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      numAt t.mem (State.addr p.base) p.w 7 = 1 ∧
      Frame [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t
  ct : ∀ {p : Inputs} {slots : List Nat} {eb1 eb2 : List Byte},
    stableSlots slots = true → 56 ∈ slots → 16 ∈ slots → 20 ∈ slots → 32 ∈ slots →
    eb1.length = p.scalarWidth → eb2.length = p.scalarWidth → p.P % 2 = 1 →
    RelCT isa (fun s t => (KeyPowerInput p slots eb1 s ∧ KeyCallMemory p s) ∧
      (KeyPowerInput p slots eb2 t ∧ KeyCallMemory p t) ∧ s.sp = t.sp) code (fun _ _ => True)

end VG.Proof.Ffdh.Arm
