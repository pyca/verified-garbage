module

public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

/-! A public bound computation installs a chosen width and mask. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure EnvironmentBoundLaw (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (code : Prog isa) : Prop where
  correct : ∀ (s : State) {p : Inputs} {slots : List Nat}
    (_h : Context p slots s) (_environment : env.holds p s)
    (_normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (_odd : p.P % 2 = 1) (_stable : stableSlots slots = true) (_slots : sampleSlots slots)
    (_h52 : 52 ∈ slots) (_h24 : 24 ∈ slots) (_h28 : 28 ∈ slots) (_h32 : 32 ∈ slots) (_h60 : 60 ∈ slots),
    WP isa code s fun t => Context p slots t ∧
      t.mem.readW (off (State.addr t.sp) 20) 32 = BitVec.ofNat 32 (layout p).width ∧
      t.mem.readW (off (State.addr t.sp) 68) 32 = (layout p).mask ∧
      Frame [⟨off (State.addr s.sp) 20, 4⟩, ⟨off (State.addr s.sp) 68, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t
  ct : ∀ {p : Inputs} {slots : List Nat}
    (_stable : stableSlots slots = true) (_slots : sampleSlots slots)
    (_normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (_odd : p.P % 2 = 1)
    (_h52 : 52 ∈ slots) (_h24 : 24 ∈ slots) (_h28 : 28 ∈ slots) (_h32 : 32 ∈ slots) (_h60 : 60 ∈ slots),
    RelCT isa (fun s t => (Context p slots s ∧ env.holds p s) ∧ (Context p slots t ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp) code (fun _ _ => True)

end VG.Proof.Ffdh.Arm
