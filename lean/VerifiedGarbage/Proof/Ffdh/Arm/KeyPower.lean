module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerPhase
public import VerifiedGarbage.Proof.Ffdh.Arm.Power
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block

/-! # Generator-specialized key-generation power after exponent and base import -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeyPower
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure Input (base src ep : BitVec 32) (len w M : Nat) (P : State → Prop)
    (regions : List Region) (bb eb : List Byte) (s : State) : Prop where
  power : PowerInput base src ep len w M bb eb s
  persistent : P s
  separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r

theorem import_ok {base src ep : BitVec 32} {len w M : Nat} {P : State → Prop}
    {regions : List Region} {bb eb : List Byte}
    (A : TwoExp.Montgomery base len w P regions) (s : State)
    (h : Input base src ep len w M P regions bb eb s) :
    WP isa VG.Impl.Ffdh.Arm.powerImport s fun t =>
      PhaseInput base ep len w M (Spec.Rsa.os2ip bb) P regions eb t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (powerImport_ok s h.power) ?_
  rintro t ⟨input, frame, rest⟩
  exact ⟨⟨input, A.stable frame rest h.persistent, h.separate⟩, frame, rest⟩

end VG.Proof.Ffdh.Arm.KeyPower
