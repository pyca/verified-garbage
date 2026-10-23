module

import VerifiedGarbage.Proof.Weierstrass.Joint
import VerifiedGarbage.Proof.Weierstrass.Comb
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! Group identities for the unsigned joint radix-four table and Horner loop. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint
open VG.Proof.Weierstrass VG.Spec.Weierstrass
variable {C : Curve}

def pair (P Q : Point C) (a b : Nat) : Point C := add (mul a P) (mul b Q)

theorem pair_curve (hC : Law C) {P Q : Point C}
    (hP : onCurve C P = true) (hQ : onCurve C Q = true) (a b : Nat) :
    onCurve C (pair P Q a b) = true :=
  hC.onCurve_add (hC.onCurve_mul hP a) (hC.onCurve_mul hQ b)

theorem pair_add (hC : Law C) {P Q : Point C}
    (hP : onCurve C P = true) (hQ : onCurve C Q = true) (a b c d : Nat) :
    add (pair P Q a b) (pair P Q c d) = pair P Q (a+c) (b+d) := by
  obtain ⟨M, _, f, hf⟩ := hC.group
  apply hf.inj (hC.onCurve_add (pair_curve hC hP hQ a b) (pair_curve hC hP hQ c d))
    (pair_curve hC hP hQ (a+c) (b+d))
  unfold pair
  rw [hf.add (hC.onCurve_add (hC.onCurve_mul hP a) (hC.onCurve_mul hQ b))
      (hC.onCurve_add (hC.onCurve_mul hP c) (hC.onCurve_mul hQ d)),
    hf.add (hC.onCurve_mul hP a) (hC.onCurve_mul hQ b),
    hf.add (hC.onCurve_mul hP c) (hC.onCurve_mul hQ d),
    hf.add (hC.onCurve_mul hP (a+c)) (hC.onCurve_mul hQ (b+d)),
    hf.mul hP, hf.mul hQ, hf.mul hP, hf.mul hQ, hf.mul hP, hf.mul hQ,
    Int.natCast_add, Int.natCast_add,
    Lean.Grind.IntModule.add_zsmul, Lean.Grind.IntModule.add_zsmul]
  grind

theorem pair_zero (P Q : Point C) : pair P Q 0 0 = .infinity := by
  have hz (T : Point C) : mul 0 T = .infinity := by rw [Spec.Weierstrass.mul]; rfl
  rw [pair,hz,hz]; rfl

theorem shift_radix (k j : Nat) :
    4 * (k >>> (2*(j+1))) + (k >>> (2*j)) % 4 = k >>> (2*j) := by
  have hs : k >>> (2*(j+1)) = (k >>> (2*j)) / 4 := by
    rw [show 2*(j+1)=2*j+2 by omega, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow]
  rw [hs]
  omega

def stage (P Q : Point C) (u v j : Nat) : Point C := pair P Q (u >>> (2*j)) (v >>> (2*j))

theorem at_step (hC : Law C) {P Q : Point C}
    (hP : onCurve C P = true) (hQ : onCurve C Q = true) (u v j : Nat) :
    add (add (add (stage P Q u v (j+1)) (stage P Q u v (j+1)))
        (add (stage P Q u v (j+1)) (stage P Q u v (j+1))))
      (pair P Q ((u >>> (2*j)) % 4) ((v >>> (2*j)) % 4)) = stage P Q u v j := by
  unfold stage
  rw [pair_add hC hP hQ, pair_add hC hP hQ, pair_add hC hP hQ]
  rw [show (u >>> (2*(j+1))) + (u >>> (2*(j+1))) +
      ((u >>> (2*(j+1))) + (u >>> (2*(j+1)))) = 4*(u >>> (2*(j+1))) by omega,
    show (v >>> (2*(j+1))) + (v >>> (2*(j+1))) +
      ((v >>> (2*(j+1))) + (v >>> (2*(j+1)))) = 4*(v >>> (2*(j+1))) by omega,
    shift_radix,shift_radix]

theorem at_zero (P Q : Point C) (u v : Nat) : stage P Q u v 0 = pair P Q u v := by
  simp only [stage,Nat.mul_zero,Nat.shiftRight_zero]

theorem at_top (P Q : Point C) {n u v : Nat} (hu : u < 2^(64*n)) (hv : v < 2^(64*n)) :
    stage P Q u v (32*n) = .infinity := by
  rw [stage,show 2*(32*n)=64*n by omega,Nat.shiftRight_eq_div_pow,Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt hu,Nat.div_eq_of_lt hv,pair_zero]

theorem pair_generator (P Q : Point C) : pair P Q 1 0 = P := by
  have hz : mul 0 Q = .infinity := by rw [Spec.Weierstrass.mul]; rfl
  rw [pair,mul_one_pt,hz,add_infinity]

theorem pair_peer (P Q : Point C) : pair P Q 0 1 = Q := by
  have hz : mul 0 P = .infinity := by rw [Spec.Weierstrass.mul]; rfl
  rw [pair,mul_one_pt,hz]; rfl

def previous (d : Nat) := if d % 4 = 0 then d-4 else d-1

theorem previous_lt {d : Nat} (hd : 1 ≤ d) : previous d < d := by
  unfold previous; split <;> omega

theorem table_step (hC : Law C) {P Q : Point C}
    (hP : onCurve C P = true) (hQ : onCurve C Q = true) {d : Nat} (hd : 1 ≤ d) :
    add (if d % 4 = 0 then Q else P)
      (pair P Q ((previous d) % 4) ((previous d) / 4)) = pair P Q (d % 4) (d / 4) := by
  by_cases hz : d % 4 = 0
  · rw [ite_eq_left hz,previous,ite_eq_left hz]
    have ee := congrArg (fun T => add T (pair P Q ((d-4)%4) ((d-4)/4))) (pair_peer P Q).symm
    rw [ee,pair_add hC hP hQ]
    have ha : 0+(d-4)%4=d%4 := by omega
    have hb : 1+(d-4)/4=d/4 := by omega
    rw [ha,hb]
  · rw [ite_eq_right hz,previous,ite_eq_right hz]
    have ee := congrArg (fun T => add T (pair P Q ((d-1)%4) ((d-1)/4))) (pair_generator P Q).symm
    rw [ee,pair_add hC hP hQ]
    have ha : 1+(d-1)%4=d%4 := by omega
    have hb : 0+(d-1)/4=d/4 := by omega
    rw [ha,hb]

theorem point_comm (hC : Law C) {P Q : Point C}
    (hP : onCurve C P=true) (hQ : onCurve C Q=true) : add P Q=add Q P := by
  obtain ⟨M,_,f,hf⟩ := hC.group
  apply hf.inj (hC.onCurve_add hP hQ) (hC.onCurve_add hQ hP)
  rw [hf.add hP hQ,hf.add hQ hP]; grind

end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint
