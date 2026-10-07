import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.SelectFields
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableState

/-! A secret magnitude selects its peer multiple and matching cached Jacobian powers. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem selectedField_point {K : WinCfg} {C : Curve} {E : Nat → Fe C} {P : Point C} {a : Nat}
    (ha : a≤16)
    (hj : ∀ j,1≤j → j≤16 → let p := Impl.Ecdh.X86_64.Window5.tablePt K j
      InvJ C (E p.x) (E p.y) (E p.z) (mul j P)) :
    InvJ C (selectedField K E a 0) (selectedField K E a 1) (selectedField K E a 2) (mul a P) := by
  by_cases h1 : 1≤a
  · simpa only [selectedField,h1,ite_true,Nat.mul_zero,Nat.add_zero,Nat.mul_one,Nat.reduceMul,
      Impl.Ecdh.X86_64.Window5.tablePt] using hj a h1 ha
  · have h0 : a=0 := by omega
    subst a
    rw [mul_zero_pt']
    apply Or.inl
    constructor
    · rfl
    · simp only [selectedField,show ¬1≤0 by omega,ite_false,show ¬(2:Nat)=1 by decide]

theorem selectedField_cache {K : WinCfg} {C : Curve} {E : Nat → Fe C} {a : Nat}
    (ha : a≤16)
    (hz : ∀ j,1≤j → j≤16 → let p := Impl.Ecdh.X86_64.Window5.tablePt K j
      E (p.x+96)=E p.z*E p.z ∧ E (p.x+128)=E (p.x+96)*E p.z) :
    selectedField K E a 3=selectedField K E a 2*selectedField K E a 2 ∧
    selectedField K E a 4=selectedField K E a 3*selectedField K E a 2 := by
  by_cases h1 : 1≤a
  · simpa only [selectedField,h1,ite_true,Nat.reduceMul,Impl.Ecdh.X86_64.Window5.tablePt] using hz a h1 ha
  · simp only [selectedField,h1,ite_false,show ¬(2:Nat)=1 by decide,
      show ¬(3:Nat)=1 by decide,show ¬(4:Nat)=1 by decide,Lean.Grind.Semiring.zero_mul,and_self]

theorem select_ok {K : WinCfg} {C : Curve} {base : Addr} {size a : Nat}
    (hL : SecretLay K size) (ht : K.tbl<2^31) (hOne : K.one<C.p)
    (hOneVal : toM C.p (2^(64*K.M.n)) K.one=1)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (·∈slots K) V E s)
    (hV : ∀ x∈tableSlots K 16,x∈V) (ha : a≤16) (h8 : s.gpr .r8=BitVec.ofNat 64 a)
    {P : Point C}
    (hj : ∀ j,1≤j → j≤16 → let p := Impl.Ecdh.X86_64.Window5.tablePt K j
      InvJ C (E p.x) (E p.y) (E p.z) (mul j P))
    (hz : ∀ j,1≤j → j≤16 → let p := Impl.Ecdh.X86_64.Window5.tablePt K j
      E (p.x+96)=E p.z*E p.z ∧ E (p.x+128)=E (p.x+96)*E p.z) :
    WP isa (.block (Impl.Ecdh.X86_64.Window5.select K)) s fun t =>
      ProgKeep K.M base (consecutiveFields K.E.x 5) s t ∧
      Inv K.M base size C.p (·∈slots K) (consecutiveFields K.E.x 5++V) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t K.E.x) (tmv C K.M.n base t K.E.y)
        (tmv C K.M.n base t K.E.z) (mul a P) ∧
      tmv C K.M.n base t (K.E.x+96)=tmv C K.M.n base t K.E.z*tmv C K.M.n base t K.E.z ∧
      tmv C K.M.n base t (K.E.x+128)=tmv C K.M.n base t (K.E.x+96)*tmv C K.M.n base t K.E.z := by
  refine WP.mono (select_fields_ok hL ht hOne hOneVal hI hV ha h8) fun t ⟨kt,it,vt⟩ => ?_
  have v0 := vt 0 (by decide)
  have v1 := vt 1 (by decide)
  have v2 := vt 2 (by decide)
  have v3 := vt 3 (by decide)
  have v4 := vt 4 (by decide)
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one,Nat.reduceMul,←hL.exy,←hL.exz] at v0 v1 v2 v3 v4
  refine ⟨kt,it,?_,?_⟩
  · rw [v0,v1,v2]
    exact selectedField_point ha hj
  · rw [v3,v4,v2]
    exact selectedField_cache ha hz

end VG.Proof.Ecdh.X86_64.Secret
