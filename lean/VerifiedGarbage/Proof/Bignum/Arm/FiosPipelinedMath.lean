module

import VerifiedGarbage.Proof.Framework.Omega

/-! One pending product joins the independent product and cancellation sums. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined

theorem start_value {R P O ca cm lo ca' V a : Nat}
    (prior : R*O+P*(ca+cm)=V) (product : lo+R*ca'=a+ca) :
    R*O+P*(lo+cm)+P*R*ca'=V+P*a := by
  have scaled := congrArg (fun z => P*z) product
  simp only [Nat.mul_add,Nat.mul_assoc,Nat.add_assoc] at *
  omega

theorem step_value {R P O O' pending ca cm next ca' cm' out V a m : Nat}
    (prior : R*O+P*(pending+cm)+P*R*ca=V)
    (product : next+R*ca'=a+ca)
    (cancel : out+R*cm'=pending+m+cm)
    (stored : R*O'=R*O+P*out) :
    R*O'+P*R*(next+cm')+P*R*R*ca'=V+P*R*a+P*m := by
  have prodScaled := congrArg (fun z => P*R*z) product
  have modScaled := congrArg (fun z => P*z) cancel
  simp only [Nat.mul_add,Nat.mul_assoc,Nat.add_assoc] at *
  omega

theorem finish_value {R P O O' pending ca cm cm' out V m : Nat}
    (prior : R*O+P*(pending+cm)+P*R*ca=V)
    (cancel : out+R*cm'=pending+m+cm)
    (stored : R*O'=R*O+P*out) :
    R*O'+P*R*(ca+cm')=V+P*m := by
  have scaled := congrArg (fun z => P*z) cancel
  simp only [Nat.mul_add,Nat.mul_assoc,Nat.add_assoc] at *
  omega

end VG.Proof.Bignum.Arm.FiosPipelined
