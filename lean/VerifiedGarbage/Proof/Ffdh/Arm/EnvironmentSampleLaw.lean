module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeySample
import VerifiedGarbage.Proof.Ffdh.Arm.SampleResult

/-! A sampling policy supplies both scalar encoding and its public execution width. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure EnvironmentSampleLaw (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (code : Prog isa) : Prop where
  correct : ∀ (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (_h : Context p slots s) (_environment : env.holds p s)
    (_normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (_odd : p.P % 2 = 1) (_stable : stableSlots slots = true) (_slots : sampleSlots slots)
    (_h52 : 52 ∈ slots) (_h0 : 0 ∈ slots) (_h24 : 24 ∈ slots) (_h28 : 28 ∈ slots) (_h32 : 32 ∈ slots)
    (_h40 : 40 ∈ slots) (_h48 : 48 ∈ slots) (_h60 : 60 ∈ slots)
    (_ready : ArithmeticReady p.base p.len p.w s)
    (_modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P)
    (_r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (_entropy : Octets p.base p.entropy p.len rb s) (_size : rb.length = p.k)
    (_entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (_outputs : KeyOutputs p s)
    (_entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩),
    WP isa code s fun t =>
      SampleContext p (layout p) slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Octets p.base p.privateValue p.len ((layout p).encode rb) t ∧
      Octets p.base (layout p).start p.len (((layout p).encode rb).drop (layout p).lead) t ∧
      Frame (keyScalarWrites p s) s.mem t.mem ∧ Rest roundClobbers s t
  ct : ∀ {p : Inputs} {slots : List Nat} {rb1 rb2 : List Byte}
    (_stable : stableSlots slots = true) (_slots : sampleSlots slots)
    (_normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (_odd : p.P % 2 = 1)
    (_h52 : 52 ∈ slots) (_h0 : 0 ∈ slots) (_h24 : 24 ∈ slots) (_h28 : 28 ∈ slots) (_h32 : 32 ∈ slots)
    (_h40 : 40 ∈ slots) (_h48 : 48 ∈ slots) (_h60 : 60 ∈ slots)
    (_size1 : rb1.length = p.k) (_size2 : rb2.length = p.k)
    (_entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩),
    RelCT isa (fun s t => (KeyScalarInput p slots rb1 s ∧ env.holds p s) ∧ (KeyScalarInput p slots rb2 t ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
      code (fun _ _ => True)

end VG.Proof.Ffdh.Arm
