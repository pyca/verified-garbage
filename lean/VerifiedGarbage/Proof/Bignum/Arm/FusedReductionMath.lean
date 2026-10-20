module

public import VerifiedGarbage.Proof.Mont.Words32

/-! The cancellation carry and the downward row together divide exactly. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FusedReduction

theorem quotient_value {B P T M t0 tl th m0 ml q c0 rl cr rh : Nat}
    (acc : T=t0+B*(tl+P*th)) (modulus : M=m0+B*ml)
    (first : B*c0=q*m0+t0) (row : rl+P*cr=tl+q*ml+c0)
    (top : rh=th+cr) : B*(rl+P*rh)=T+q*M := by
  have step := congrArg (fun x => B*x) row
  grind

end VG.Proof.Bignum.Arm.FusedReduction
