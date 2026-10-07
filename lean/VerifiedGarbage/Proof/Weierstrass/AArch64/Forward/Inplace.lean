import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Arithmetic
import VerifiedGarbage.Proof.Weierstrass.JacInplace

namespace VG.Proof.Weierstrass.AArch64.Forward.Arithmetic
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

private theorem inplace_reads (S : RcbSlots) (p : Pt) :
    readsOk (dblJMul S p p) [p.x,p.y,p.z]=true := by
  have h : readsOk (dblJMul ⟨9,10,0,1,2,3,4,5⟩ ⟨6,7,8⟩ ⟨6,7,8⟩) [6,7,8]=true := by decide
  exact readsOk_rename (rcbσ S p p p) h

private theorem inplace_slots (S : RcbSlots) (p : Pt) :
    ∀ op∈dblJMul S p p,∀ x∈op.out::op.ins,x∈rcbW S p := by
  simp [dblJMul,FOp.out,FOp.ins,rcbW]

/-- The output aliases the input, while the scratch slots remain distinct. -/
theorem double_ok (certs : Cases) {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod C.p (2^(64*M.n))) (hsize : 8192≤size) (hC : Law C) (ha : AM3 C)
    {S : RcbSlots} {p : Pt} (hA : (rcbW S p).Nodup)
    (hSl : ∀ x∈rcbW S p,Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv M base size C.p Sl V E s)
    (hV : ∀ x∈[p.x,p.y,p.z],x∈V) {P : Point C}
    (hP : onCurve C P=true) (hJ : InvJ C (E p.x) (E p.y) (E p.z) P) :
    WP isa (VG.Impl.P256.VerifyArithmetic.double M S p) s fun t =>
      ProgKeep M base (rcbW S p) s t ∧
      Inv M base size C.p Sl V (runOps (dblJMul S p p) E) t ∧
      InvJ C (runOps (dblJMul S p p) E p.x) (runOps (dblJMul S p p) E p.y)
        (runOps (dblJMul S p p) E p.z) (Spec.Weierstrass.add P P) := by
  refine WP.mono (field_ok certs hL hAl hm hsize (dblJMul S p p) hI
    (fun op hop x hx => hSl x (inplace_slots S p op hop x hx))
    (readsOk_mono (inplace_reads S p) hV)) fun t ⟨hk,hi⟩ => ⟨?_,?_,?_⟩
  · exact hk.mono fun x hx => by
      obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
      exact inplace_slots S p op hop op.out (by simp)
  · exact hi.sub fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
  · exact InvJ.dbl' hC ha hP hJ (dblJMul_inplace_run hA E)

/-- Equal public coordinates give equal in-place outputs and traces. -/
theorem double_relCT (certs : Cases) {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2^(64*M.n))) (hsize : 8192≤size) {S : RcbSlots} {p : Pt}
    (hSl : ∀ x∈rcbW S p,Sl x) {V : List Nat} {E : Nat → Fin m}
    (hV : ∀ x∈[p.x,p.y,p.z],x∈V)
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
      (VG.Impl.P256.VerifyArithmetic.double M S p)) :
    RelCT isa (FieldPair M base size m Sl V E) (VG.Impl.P256.VerifyArithmetic.double M S p)
      (FieldPair M base size m Sl V (runOps (dblJMul S p p) E)) := by
  exact (field_relCT certs hL hAl hm hsize (dblJMul S p p)
    (fun op hop x hx => hSl x (inplace_slots S p op hop x hx))
    (readsOk_mono (inplace_reads S p) hV) hct).mono (fun _ _ h => h)
      (fun _ _ h => h.sub (fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)))

end VG.Proof.Weierstrass.AArch64.Forward.Arithmetic
