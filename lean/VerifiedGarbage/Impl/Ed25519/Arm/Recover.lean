import VerifiedGarbage.Impl.Ed25519.Arm.Power
import VerifiedGarbage.Impl.Ed25519.Arm.FieldCheck

/-! Recover the candidate x-coordinate and its square check from y in slot 1. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def recoverInitOps : List FieldOp := [
  .const 16 Spec.Ed25519.d, .const 4 1, .mulc 5 1 1, .sub 6 5 4,
  .mulc 7 16 1, .mulc 7 7 1, .add 7 7 4,
  .mulc 8 7 7, .mulc 9 8 7, .mulc 10 9 9, .mulc 10 10 7, .mulc 2 6 10]

def recoverFinishOps : List FieldOp := [
  .const 5 0, .sub 12 5 6, .mulc 0 6 9, .mulc 0 0 15, .mulc 11 7 0, .mulc 11 11 0]

def recoverCandidate : Prog isa :=
  .seq (fieldCode recoverInitOps) (.seq rootPower (fieldCode recoverFinishOps))

end VG.Impl.Ed25519.Arm
