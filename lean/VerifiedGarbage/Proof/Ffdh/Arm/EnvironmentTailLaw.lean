module

public import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTail
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.SamplePowerLaw

public import VerifiedGarbage.TCB.Arm.Isa

/-! # The public-value exponentiation boundary of a key-generation attempt -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)

structure EnvironmentTailLaw (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (code : Prog isa) : Prop where
  correct : ∀ (s : State) {p : Inputs} {slots : List Nat} {xb eb : List Byte}
    (_h : SampleContext p (layout p) slots s) (_environment : env.holds p s) (_calls : KeyCallMemory p s) (_stable : stableSlots slots = true)
    (_h52 : 52 ∈ slots) (_h4 : 4 ∈ slots) (_h32 : 32 ∈ slots)
    (_h36 : 36 ∈ slots) (_h40 : 40 ∈ slots) (_h56 : 56 ∈ slots)
    (_saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (_ready : ArithmeticReady p.base p.len p.w s)
    (_modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (_odd : p.P % 2 = 1)
    (_r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (_scalar : Octets p.base p.privateValue p.len xb s) (_scalarSize : xb.length = p.k)
    (_scalarFits : Spec.Rsa.os2ip xb < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (_significant : Octets p.base (layout p).start p.len eb s) (_significantSize : eb.length = (layout p).width)
    (_significantValue : Spec.Rsa.os2ip eb = Spec.Rsa.os2ip xb)
    (_outputs : KeyOutputs p s) (_outputY : p.output = p.publicValue),
    WP isa code s fun t =>
      t.gpr .r0 = (if keyAccepted p xb then 1 else 3) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k =
        (if keyAccepted p xb then xb else List.replicate p.k 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k =
        (if keyAccepted p xb then Spec.Rsa.i2osp (keyPower p xb) p.k else List.replicate p.k 0) ∧
      Frame (keyCallWrites p s) s.mem t.mem
  ct : ∀ {p : Inputs} {slots : List Nat} {eb1 eb2 : List Byte}
    (_stable : stableSlots slots = true) (_h52 : 52 ∈ slots) (_h4 : 4 ∈ slots) (_h32 : 32 ∈ slots)
    (_h36 : 36 ∈ slots) (_h40 : 40 ∈ slots) (_h56 : 56 ∈ slots)
    (_saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (_size1 : eb1.length = (layout p).width) (_size2 : eb2.length = (layout p).width)
    (_fit1 : Spec.Rsa.os2ip eb1 < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (_fit2 : Spec.Rsa.os2ip eb2 < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (_odd : p.P % 2 = 1) (_outputY : p.output = p.publicValue),
    RelCT isa (fun s t => ((SamplePowerInput p (layout p) slots eb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((SamplePowerInput p (layout p) slots eb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
      code (fun _ _ => True)

end VG.Proof.Ffdh.Arm
