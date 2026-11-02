module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowPhase
public import VerifiedGarbage.Proof.Bignum.Arm.WindowPhaseCT

/-! The CRT pipeline uses one exponentiation proof for every arithmetic kernel. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest)

structure WindowKernel where
  code : Prog isa
  correct : ∀ (s : State) {base ep : BitVec 32} {len w M x : Nat} {eb : List Byte},
    ExpPhaseInput base ep len w M x eb s → arrAt w 16 ≤ 8 * len →
    WP isa code s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod x (Spec.Rsa.os2ip eb) M ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧
      numAt t.mem (State.addr base) w 7 = 1 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t
  ct : ∀ {base ep : BitVec 32} {len w M1 M2 x1 x2 : Nat} {eb1 eb2 : List Byte},
    arrAt w 3 + 32 ≤ 8 * len → arrAt w 16 ≤ 8 * len → 0 < eb1.length →
    eb1.length = eb2.length →
    RelCT isa (fun s t => ExpPhaseInput base ep len w M1 x1 eb1 s ∧
      ExpPhaseInput base ep len w M2 x2 eb2 t ∧ s.sp = t.sp) code (fun _ _ => True)

def baselineWindowKernel : WindowKernel where
  code := windowExpPhase
  correct := windowExpPhase_ok
  ct := windowExpPhase_ct

end VG.Proof.Bignum.Arm
