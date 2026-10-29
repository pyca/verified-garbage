module

public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Omega
/-! Lift the carry identities to Montgomery operand prefixes. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/FiosPipelinedMath.lean`, which only this module imported.
section

/-! One pending product joins the independent product and cancellation sums. -/

section
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
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined
open VG VG.Proof.Mont

theorem start_prefix {mem0 mem : Mem} {base : Addr} {acc b mod i x q ca cm lo ca' : Nat}
    (prior : 2^32*val32 mem base acc i+2^(32*(i+1))*(ca+cm)=
      val32 mem0 base acc (i+1)+x*val32 mem0 base b (i+1)+q*val32 mem0 base mod (i+1))
    (product : lo+2^32*ca'=w32 mem0 base (acc+4*(i+1))+x*w32 mem0 base (b+4*(i+1))+ca) :
    2^32*val32 mem base acc i+2^(32*(i+1))*(lo+cm)+2^(32*(i+2))*ca'=
      val32 mem0 base acc (i+2)+x*val32 mem0 base b (i+2)+q*val32 mem0 base mod (i+1) := by
  have power : 2^(32*(i+2))=2^(32*(i+1))*2^32 :=
    (pow32_succ (i+1)).trans (Nat.mul_comm _ _)
  rw [power]
  refine (start_value prior product).trans ?_
  rw [val32_succ mem0 base acc (i+1),val32_succ mem0 base b (i+1)]
  simp only [Nat.mul_add]
  ac_rfl

theorem step_prefix {mem0 mem mem' : Mem} {base : Addr}
    {acc b mod i x q pending ca cm next ca' cm' out : Nat}
    (prior : 2^32*val32 mem base acc i+2^(32*(i+1))*(pending+cm)+2^(32*(i+2))*ca=
      val32 mem0 base acc (i+2)+x*val32 mem0 base b (i+2)+q*val32 mem0 base mod (i+1))
    (product : next+2^32*ca'=w32 mem0 base (acc+4*(i+2))+x*w32 mem0 base (b+4*(i+2))+ca)
    (cancel : out+2^32*cm'=pending+q*w32 mem0 base (mod+4*(i+1))+cm)
    (stored : val32 mem' base acc (i+1)=val32 mem base acc i+2^(32*i)*out) :
    2^32*val32 mem' base acc (i+1)+2^(32*(i+2))*(next+cm')+2^(32*(i+3))*ca'=
      val32 mem0 base acc (i+3)+x*val32 mem0 base b (i+3)+q*val32 mem0 base mod (i+2) := by
  have power : 2^(32*(i+2))=2^(32*(i+1))*2^32 :=
    (pow32_succ (i+1)).trans (Nat.mul_comm _ _)
  have powerNext : 2^(32*(i+3))=2^(32*(i+1))*2^32*2^32 := by
    rw [pow32_succ (i+2),power]
    rw [←Nat.mul_assoc (2^32) (2^(32*(i+1))) (2^32),
      Nat.mul_comm (2^32) (2^(32*(i+1)))]
  have ready := prior
  rw [power] at ready
  have write := congrArg (fun z => 2^32*z) stored
  simp only [Nat.mul_add] at write
  have scale : 2^32*2^(32*i)=2^(32*(i+1)) :=
    (pow32_succ i).symm
  rw [←Nat.mul_assoc (2^32) (2^(32*i)) out,scale] at write
  rw [power,powerNext]
  refine (step_value ready product cancel write).trans ?_
  rw [val32_succ mem0 base acc (i+2),val32_succ mem0 base b (i+2),
    val32_succ mem0 base mod (i+1),power]
  simp only [Nat.mul_add]
  ac_rfl

theorem finish_prefix {mem0 mem mem' : Mem} {base : Addr}
    {acc b mod i x q pending ca cm cm' out : Nat}
    (prior : 2^32*val32 mem base acc i+2^(32*(i+1))*(pending+cm)+2^(32*(i+2))*ca=
      val32 mem0 base acc (i+2)+x*val32 mem0 base b (i+2)+q*val32 mem0 base mod (i+1))
    (cancel : out+2^32*cm'=pending+q*w32 mem0 base (mod+4*(i+1))+cm)
    (stored : val32 mem' base acc (i+1)=val32 mem base acc i+2^(32*i)*out) :
    2^32*val32 mem' base acc (i+1)+2^(32*(i+2))*(ca+cm')=
      val32 mem0 base acc (i+2)+x*val32 mem0 base b (i+2)+q*val32 mem0 base mod (i+2) := by
  have power : 2^(32*(i+2))=2^(32*(i+1))*2^32 :=
    (pow32_succ (i+1)).trans (Nat.mul_comm _ _)
  have ready := prior
  rw [power] at ready
  have write := congrArg (fun z => 2^32*z) stored
  simp only [Nat.mul_add] at write
  have scale : 2^32*2^(32*i)=2^(32*(i+1)) :=
    (pow32_succ i).symm
  rw [←Nat.mul_assoc (2^32) (2^(32*i)) out,scale] at write
  rw [power]
  refine (finish_value ready cancel write).trans ?_
  rw [val32_succ mem0 base mod (i+1)]
  simp only [Nat.mul_add]
  ac_rfl

end VG.Proof.Bignum.Arm.FiosPipelined
