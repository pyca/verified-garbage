module

public import VerifiedGarbage.Proof.Bignum.Arm.Precompute
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputePublicCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
public import VerifiedGarbage.Proof.Framework.RelCT

/-! Public-key setup callers share one code and proof interface. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

structure PublicPrecomputeKernel where
  code : Prog isa
  correct : PrecomputeLaw code
  ct : ∀ {base src : BitVec 32} {len w k : Nat} {nb : List Byte},
    128 * w < 2 ^ 32 → RelCT isa (fun s t =>
      (PrecomputeInput base src len w k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) ∧
      (PrecomputeInput base src len w k t ∧ Spec.Rsa.bytesAt t.mem (State.addr src) k = nb) ∧ s.sp = t.sp)
      code (fun _ _ => True)

def baselinePublicPrecomputeKernel : PublicPrecomputeKernel where
  code := precompute
  correct := precompute_ok
  ct := by
    intro base src len w k nb fits
    exact (precompute_ct fits).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Bignum.Arm
