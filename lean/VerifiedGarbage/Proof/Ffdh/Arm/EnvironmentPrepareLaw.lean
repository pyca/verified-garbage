module

public import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack

/-! # Modulus preparation shared by key-generation arithmetic backends

The public modulus gate supplies the lower bound for its packed-word width.
Preparation may use that normalization without adding a caller obligation to
FFDH's shared contract.
-/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure EnvironmentPrepareLaw (env : SampleEnvironment) (code : Prog isa) : Prop where
  correct : ∀ (s : State) {p : Inputs} {slots : List Nat}
    (_h : Context p slots s) (_environment : env.holds p s) (_calls : KeyCallMemory p s)
    (_stable : stableSlots slots = true) (_h52 : 52 ∈ slots) (_h0 : 0 ∈ slots) (_h24 : 24 ∈ slots) (_h32 : 32 ∈ slots)
    (_large : 1 < p.P) (_odd : p.P % 2 = 1) (_normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P),
    WP isa code s fun t => Context p slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Frame (keyPrepareWrites p s) s.mem t.mem ∧ Rest roundClobbers s t
  ct : ∀ {p : Inputs} {slots : List Nat}
    (_stable : stableSlots slots = true) (_h52 : 52 ∈ slots) (_h0 : 0 ∈ slots) (_h24 : 24 ∈ slots) (_h32 : 32 ∈ slots)
    (_large : 1 < p.P) (_odd : p.P % 2 = 1) (_normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P),
    RelCT isa (fun s t => ((Context p slots s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((Context p slots t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp) code (fun _ _ => True)

end VG.Proof.Ffdh.Arm
