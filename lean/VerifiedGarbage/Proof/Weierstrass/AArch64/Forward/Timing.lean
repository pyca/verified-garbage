import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Selected
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64

/-- The selected register forwarding preserves the complete field environment. -/
theorem field_ok (certs : Fixed.Cases) {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl) (hnc : Mont.callOf M = none)
    (hm : UnitMod m (2^(64*M.n))) {S : RcbSlots} {p o : Pt} (hA : RcbApart S p p o)
    (hSl : ∀ x∈rcbW S o ++ rcbR S p p,Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s)
    (hV : ∀ x∈rcbR S p p,x∈V) :
    WP isa (VG.Impl.P256.VerifyDouble.double M S p o) s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size m Sl ([o.x,o.y,o.z]++V) (runOps (dblJMul S p o) E) t := by
  have baseline : WP isa (fprogB M (dblJMul S p o)) s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size m Sl ([o.x,o.y,o.z]++V) (runOps (dblJMul S p o) E) t := by
    have he : dblJMul S p o=ofN (dblJChoiceN true) S p p o := dblJChoice_eq true S p o
    rw [he]
    exact WP.mono (ofN_ok hL hAl hm (dblJChoiceN_ok true) hA hSl (.inl hnc) hI hV)
      fun _ ⟨hk,hi,_⟩ => ⟨hk,hi⟩
  by_cases sel : VG.Impl.P256.VerifyDouble.selected M S p o
  · exact WP.mono (selected_refinement certs sel hL hSl hI.scr baseline)
      fun _ ⟨_,⟨hk,hi⟩,he,kt⟩ => transfer_post he kt hk hi
  · rw [VG.Impl.P256.VerifyDouble.double,ite_eq_right sel]
    exact baseline

/-- The same relational transition also exposes the newly written coordinates. -/
theorem field_outputs_relCT (certs : Fixed.Cases) {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl) (hnc : Mont.callOf M = none)
    (hm : UnitMod m (2^(64*M.n))) {S : RcbSlots} {p o : Pt} (hA : RcbApart S p p o)
    (hSl : ∀ x∈rcbW S o ++ rcbR S p p,Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR S p p,x∈V)
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
      (VG.Impl.P256.VerifyDouble.double M S p o)) :
    RelCT isa (FieldPair M base size m Sl V E) (VG.Impl.P256.VerifyDouble.double M S p o)
      (FieldPair M base size m Sl ([o.x,o.y,o.z]++V) (runOps (dblJMul S p o) E)) := by
  exact fieldWP_relCT hct fun _ hi => WP.mono (field_ok certs hL hAl hnc hm hA hSl hi hV)
    fun _ ⟨hk,it⟩ => ⟨it,hk.sp⟩

/-- Fixed field inputs determine both the forwarded output values and trace. -/
theorem field_relCT (certs : Fixed.Cases) {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl) (hnc : Mont.callOf M = none)
    (hm : UnitMod m (2^(64*M.n))) {S : RcbSlots} {p o : Pt} (hA : RcbApart S p p o)
    (hSl : ∀ x∈rcbW S o ++ rcbR S p p,Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR S p p,x∈V)
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
      (VG.Impl.P256.VerifyDouble.double M S p o)) :
    RelCT isa (FieldPair M base size m Sl V E) (VG.Impl.P256.VerifyDouble.double M S p o)
      (FieldPair M base size m Sl V (runOps (dblJMul S p o) E)) := by
  exact fieldWP_relCT hct fun _ hi => WP.mono (field_ok certs hL hAl hnc hm hA hSl hi hV)
    fun _ ⟨hk,it⟩ => ⟨it.sub (fun _ hx => List.mem_append_right _ hx),hk.sp⟩

end VG.Proof.Weierstrass.AArch64.Forward
