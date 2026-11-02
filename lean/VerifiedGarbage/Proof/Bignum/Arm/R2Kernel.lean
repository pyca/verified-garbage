module

public import VerifiedGarbage.Proof.Bignum.Arm.R2

/-! One correctness interface for the existing and normalized R-squared calculations. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure R2Kernel where
  code : Prog isa
  correct : ∀ (s : State) {base : BitVec 32} {len w : Nat},
    ArithmeticReady base len w s → 128 * w < 2 ^ 32 →
    WP isa code s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t

def baselineR2Kernel : R2Kernel := ⟨r2, r2_ok⟩

end VG.Proof.Bignum.Arm
