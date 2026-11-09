module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishGroup

/-! The final digit's group representative supplies the existing ECDH exchange
specification, with invalid scalar and invalid peer paths kept explicit. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.Proof.Weierstrass VG.Proof.Ecdh Spec.Weierstrass Spec.EcKey

 theorem finish_exchange_eq {C : Curve} (law : Law C) (ha : AM3 C)
    {d : Nat} {bs : List Byte} (hlen : bs.length=2*C.len+1) {b0 : Byte}
    (hb0 : bs.head?=some b0) {x y : Nat} (hxv : ofBytes ((bs.drop 1).take C.len)=x)
    (hyv : ofBytes (bs.drop (C.len+1))=y) {P : Point C}
    (hP : onCurve C P=true)
    (selected : ∀h : Valid C b0 x y,P=.affine ⟨x,h.2.1⟩ ⟨y,h.2.2.1⟩)
    {A D : Fe C×Fe C×Fe C}
    (accumulator : d<C.n → InvJ C A.1 A.2.1 A.2.2 (mul (Window5.winE (d+16*Window5.geom 105) 105 1) P))
    (digit : d<C.n → RepA C D.1 D.2.1 D.2.2 (Window5.winPt C P (d+16*Window5.geom 105) 0))
    {xo : Nat} (bound : xo<C.p)
    (value : Fin.ofNat C.p xo=(finalSum A D).1*(finalSum A D).2.2^(C.p-2)) :
    Spec.Ecdh.exchange C d bs=
      if ((Valid C b0 x y ∧ 0<d ∧ d<C.n) ∧ (finalSum A D).2.2≠0)
      then some (toBytes C.len xo) else none := by
  have result := exchange_eq_of_lt law hlen hb0 hxv hyv selected
    (fun hd => final_digit_group law ha hP (accumulator hd) (digit hd)) bound value
  have reorder : ((1≤d ∧ d<C.n) ∧ Valid C b0 x y ∧ (finalSum A D).2.2≠0) ↔
      ((Valid C b0 x y ∧ 0<d ∧ d<C.n) ∧ (finalSum A D).2.2≠0) := by
    constructor
    · rintro ⟨⟨lo,hi⟩,valid,nz⟩
      exact ⟨⟨valid,lo,hi⟩,nz⟩
    · rintro ⟨⟨valid,lo,hi⟩,nz⟩
      exact ⟨⟨lo,hi⟩,valid,nz⟩
  simpa only [reorder] using result

end VG.Proof.Weierstrass.AArch64.P521Native
