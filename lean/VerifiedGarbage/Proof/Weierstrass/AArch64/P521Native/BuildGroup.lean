module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildMixedCode
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleOutput
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.WinJacMath
public import VerifiedGarbage.Proof.Weierstrass.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.JacMadd

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass

theorem build_mixed_verified {s : State} {base : Addr} {W : Nat}
    (hs : Scr s base W) (hW : 4024≤W) (hMax : W≤8192)
    (px : wordsVal s.mem base 2800 9<fieldPrime)
    (py : wordsVal s.mem base 3160 9<fieldPrime)
    (rx : wordsVal s.mem base 1504 9<fieldPrime)
    (ry : wordsVal s.mem base 1576 9<fieldPrime) (rz : wordsVal s.mem base 1648 9<fieldPrime) :
    WP isa buildMixedMachine s fun t =>
      canonicalPoint t.mem base 1288 ∧
      ordinaryPoint t.mem base 1288=maddJF (Fin.ofNat fieldPrime (wordsVal s.mem base 1504 9))
        (Fin.ofNat fieldPrime (wordsVal s.mem base 1576 9)) (Fin.ofNat fieldPrime (wordsVal s.mem base 1648 9))
        (Fin.ofNat fieldPrime (wordsVal s.mem base 2800 9)) (Fin.ofNat fieldPrime (wordsVal s.mem base 3160 9)) ∧
      Scr t base W ∧ FieldPublic s t ∧ FieldProgramFrame base id buildMixedOps s.mem t.mem := by
  let E : Nat → Fin fieldPrime := fun d => Fin.ofNat fieldPrime (wordsVal s.mem base d 9)
  have inv : OrdinaryInv base fieldPrime id [1504,1576,1648,2800,3160] E (fun _ => 1) s := by
    constructor
    · intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl
      · simpa only [Nat.one_mul,id] using rx
      · simpa only [Nat.one_mul,id] using ry
      · simpa only [Nat.one_mul,id] using rz
      · simpa only [Nat.one_mul,id] using px
      · simpa only [Nat.one_mul,id] using py
    · intro x _; rfl
  apply build_mixed_machine_wp.mpr
  refine WP.mono (field_program_ok hW hMax build_field_layout buildMixedOps hs inv
    (by intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl|rfl <;> simp [buildSlot])
    buildMixed_slots buildMixed_reads buildMixed_coeffs) fun t ⟨it,ht,pt,ft⟩ => ?_
  have bx := it.bound 1288 (by decide)
  have byy := it.bound 1360 (by decide)
  have bz := it.bound 1432 (by decide)
  have vx := it.value 1288 (by decide)
  have vy := it.value 1360 (by decide)
  have vz := it.value 1432 (by decide)
  simp only [id] at vx vy vz
  refine ⟨⟨?_,?_,?_⟩,?_,ht,pt,ft⟩
  · simpa only [id,Nat.one_mul] using bx
  · simpa only [id,Nat.one_mul] using byy
  · simpa only [id,Nat.one_mul] using bz
  · change (Fin.ofNat fieldPrime (wordsVal t.mem base 1288 9),
      Fin.ofNat fieldPrime (wordsVal t.mem base 1360 9),Fin.ofNat fieldPrime (wordsVal t.mem base 1432 9))=_
    rw [vx,vy,vz]
    exact buildMixed_value E

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG.Proof.Weierstrass Spec.Weierstrass

theorem madd_coordinate_transfer {C : Curve} {p : Nat} [NeZero p]
    (hp : C.p=p) (law : Law C) (ha : AM3 C)
    {X Y Z x y X' Y' Z' : Nat} {Q : Point C}
    (value : (Fin.ofNat p X',Fin.ofNat p Y',Fin.ofNat p Z')=
      maddJF (Fin.ofNat p X) (Fin.ofNat p Y) (Fin.ofNat p Z) (Fin.ofNat p x) (Fin.ofNat p y))
    (hQ : onCurve C Q=true)
    (hPeer : onCurve C (.affine (Fin.ofNat C.p x) (Fin.ofNat C.p y))=true)
    (current : InvJ C (Fin.ofNat C.p X) (Fin.ofNat C.p Y) (Fin.ofNat C.p Z) Q)
    (nonzero : Q≠.infinity) (separate : Q≠.affine (Fin.ofNat C.p x) (Fin.ofNat C.p y)) :
    InvJ C (Fin.ofNat C.p X') (Fin.ofNat C.p Y') (Fin.ofNat C.p Z')
      (Spec.Weierstrass.add Q (.affine (Fin.ofNat C.p x) (Fin.ofNat C.p y))) := by
  rcases C with ⟨q,a,b,gx,gy,n,len,qnz,nnz⟩
  dsimp only at hp
  subst q
  have hz := mt ((InvJ.z_zero_iff law current).mp) nonzero
  have result := InvJ.madd law ha hQ hPeer current hz separate
  rw [←value] at result
  exact result

theorem dbl_coordinate_transfer {C : Curve} {p : Nat} [NeZero p]
    (hp : C.p=p) (law : Law C) (ha : AM3 C)
    {X Y Z X' Y' Z' : Nat} {Q : Point C}
    (value : (Fin.ofNat p X',Fin.ofNat p Y',Fin.ofNat p Z')=
      dblJF (Fin.ofNat p X) (Fin.ofNat p Y) (Fin.ofNat p Z))
    (hQ : onCurve C Q=true)
    (current : InvJ C (Fin.ofNat C.p X) (Fin.ofNat C.p Y) (Fin.ofNat C.p Z) Q) :
    InvJ C (Fin.ofNat C.p X') (Fin.ofNat C.p Y') (Fin.ofNat C.p Z')
      (Spec.Weierstrass.add Q Q) := by
  rcases C with ⟨q,a,b,gx,gy,n,len,qnz,nnz⟩
  dsimp only at hp
  subst q
  have result := InvJ.dbl law ha hQ current
  rw [←value] at result
  exact result

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass Spec.Weierstrass

def pointAt (C : Curve) (m : Mem) (base : Addr) (d : Nat) : Fe C × Fe C × Fe C :=
  (Fin.ofNat C.p (wordsVal m base d 9),Fin.ofNat C.p (wordsVal m base (d+72) 9),
    Fin.ofNat C.p (wordsVal m base (d+144) 9))

def peerPoint (C : Curve) (m : Mem) (base : Addr) : Point C :=
  .affine (Fin.ofNat C.p (wordsVal m base 2800 9)) (Fin.ofNat C.p (wordsVal m base 3160 9))

theorem build_mixed_group {C : Curve} (hp : C.p=fieldPrime) (law : Law C) (ha : AM3 C)
    {s : State} {base : Addr} {W : Nat} {Q : Point C}
    (hs : Scr s base W) (hW : 4024≤W) (hMax : W≤8192)
    (px : wordsVal s.mem base 2800 9<fieldPrime) (py : wordsVal s.mem base 3160 9<fieldPrime)
    (rx : wordsVal s.mem base 1504 9<fieldPrime) (ry : wordsVal s.mem base 1576 9<fieldPrime)
    (rz : wordsVal s.mem base 1648 9<fieldPrime)
    (hQ : onCurve C Q=true) (hPeer : onCurve C (peerPoint C s.mem base)=true)
    (current : InvJ C (pointAt C s.mem base 1504).1 (pointAt C s.mem base 1504).2.1
      (pointAt C s.mem base 1504).2.2 Q)
    (nonzero : Q≠.infinity) (separate : Q≠peerPoint C s.mem base) :
    WP isa buildMixedMachine s fun t =>
      canonicalPoint t.mem base 1288 ∧
      InvJ C (pointAt C t.mem base 1288).1 (pointAt C t.mem base 1288).2.1
        (pointAt C t.mem base 1288).2.2 (Spec.Weierstrass.add Q (peerPoint C s.mem base)) ∧
      Scr t base W ∧ FieldPublic s t ∧ FieldProgramFrame base id buildMixedOps s.mem t.mem := by
  refine WP.mono (build_mixed_verified hs hW hMax px py rx ry rz) fun t ⟨bound,value,ht,pt,ft⟩ => ?_
  exact ⟨bound,madd_coordinate_transfer hp law ha value hQ hPeer current nonzero separate,ht,pt,ft⟩

end VG.Proof.Weierstrass.AArch64.P521Native
