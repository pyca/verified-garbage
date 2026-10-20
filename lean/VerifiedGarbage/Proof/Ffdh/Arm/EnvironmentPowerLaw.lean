module

public import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment

public import VerifiedGarbage.Proof.Ffdh.Arm.SamplePowerLaw
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerAt
public import VerifiedGarbage.Proof.Ffdh.Arm.Context

/-! # The shared key-generation exponentiator's caller contract -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure EnvironmentPowerLaw (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (code : Prog isa) : Prop where
  correct : ∀ (s : State) {p : Inputs} {slots : List Nat} {eb : List Byte},
    SampleContext p (layout p) slots s → env.holds p s → KeyCallMemory p s → stableSlots slots = true →
    52 ∈ slots → 56 ∈ slots → 32 ∈ slots →
    ArithmeticReady p.base p.len p.w s →
    numAt s.mem (State.addr p.base) p.w 0 = p.P → p.P % 2 = 1 →
    numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P →
    Octets p.base (layout p).start p.len eb s → eb.length = (layout p).width →
    Spec.Rsa.os2ip eb < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom) →
    WP isa code s fun t => Context p slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 6 = Spec.Rsa.powMod p.G (Spec.Rsa.os2ip eb) p.P ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      numAt t.mem (State.addr p.base) p.w 7 = 1 ∧
      Frame [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t
  ct : ∀ {p : Inputs} {slots : List Nat} {eb1 eb2 : List Byte},
    stableSlots slots = true → 52 ∈ slots → 56 ∈ slots → 32 ∈ slots →
    eb1.length = (layout p).width → eb2.length = (layout p).width →
    Spec.Rsa.os2ip eb1 < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom) →
    Spec.Rsa.os2ip eb2 < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom) → p.P % 2 = 1 →
    RelCT isa (fun s t => ((SamplePowerInput p (layout p) slots eb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((SamplePowerInput p (layout p) slots eb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp) code (fun _ _ => True)

end VG.Proof.Ffdh.Arm
