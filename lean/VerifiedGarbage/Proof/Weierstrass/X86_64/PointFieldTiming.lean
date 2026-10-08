import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacAdd

/-! Exact common field environments for the exceptional point-addition branches. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64

def copyPointEnv {F : Type _} (E : Nat → F) (o q : Pt) : Nat → F :=
  let e₁ := Function.update E o.x (E q.x)
  let e₂ := Function.update e₁ o.y (e₁ q.y)
  Function.update e₂ o.z (e₂ q.z)

theorem copyPoint_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    {o q : Pt} (hSl : ∀ x∈[o.x,o.y,o.z], Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈[q.x,q.y,q.z], x∈V)
    (hct : ScratchCT (.block (copyPt M.n o q))) :
    RelCT isa (FieldPair M base size m Sl V E) (.block (copyPt M.n o q))
      (FieldPair M base size m Sl ([o.x,o.y,o.z]++V) (copyPointEnv E o q)) := by
  apply fieldProgram_relCT hct
  intro s hi
  rw [copyPt,List.append_assoc,WP.block_append_iff]
  refine WP.mono (copyField_ok hL hi (hSl _ (by simp)) (hV _ (by simp))) fun a ⟨_,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok hL ia (hSl _ (by simp))
    (List.mem_cons_of_mem _ (hV _ (by simp)))) fun b ⟨_,ib⟩ => ?_
  refine WP.mono (copyField_ok hL ib (hSl _ (by simp))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hV _ (by simp))))) fun t ⟨_,it⟩ => ?_
  apply it.sub
  intro x hx
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

def infinityEnv (M : Mod) (m one : Nat) [NeZero m] (E : Nat → Fin m) (o : Pt) : Nat → Fin m :=
  Function.update (Function.update (Function.update E o.x (toM m (2^(64*M.n)) 0))
    o.y (toM m (2^(64*M.n)) one)) o.z (toM m (2^(64*M.n)) 0)

theorem infinity_relCT {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl)
    {o : Pt} (hSl : ∀ x∈[o.x,o.y,o.z], Sl x) (hOne : K.one<m)
    {V : List Nat} {E : Nat → Fin m} (hct : ScratchCT (.block (Jacobian.infinity K o))) :
    RelCT isa (FieldPair K.M base size m Sl V E) (.block (Jacobian.infinity K o))
      (FieldPair K.M base size m Sl ([o.x,o.y,o.z]++V) (infinityEnv K.M m K.one E o)) := by
  apply fieldProgram_relCT hct
  intro s hi
  have hR := wordsVal_lt s.mem base K.M.mo K.M.n
  rw [hi.mod.val] at hR
  have h0 : 0<m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [Jacobian.infinity,List.append_assoc,WP.block_append_iff]
  refine WP.mono (setField_ok hL hi (hSl _ (by simp)) h0 hR) fun a ⟨_,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setField_ok hL ia (hSl _ (by simp)) hOne hR) fun b ⟨_,ib⟩ => ?_
  refine WP.mono (setField_ok hL ib (hSl _ (by simp)) h0 hR) fun t ⟨_,it⟩ => ?_
  apply it.sub
  intro x hx
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem ofN_forward_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) {N : List FOp} (hN : NumOk N)
    {S : RcbSlots} {p q o : Pt}
    (hSl : ∀ x∈rcbW S o++rcbR S p q,Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR S p q,x∈V)
    (hc : ScratchCT (ForwardField.programB M (ofN N S p q o)).inline) :
    RelCT isa (FieldPair M base size m Sl V E) (ForwardField.programB M (ofN N S p q o)).inline
      (FieldPair M base size m Sl ([o.x,o.y,o.z]++V) (runOps (ofN N S p q o) E)) := by
  apply fieldProgram_relCT hc
  intro s hi
  refine WP.mono (ForwardField.programB_ok hL hm _ hi
    (fun op hop x hx => hSl x (ofN_slots op hop x hx))
    (readsOk_mono (ofN_readsOk hN S p q o) hV)) fun _ ht => ht.2.sub ?_
  intro x hx
  rw [mem_validAfter]
  rcases List.mem_append.mp hx with hx|hx
  · exact Or.inr (ofN_out_mem hN hx)
  · exact Or.inl hx

theorem doubleField_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) {S : RcbSlots} {p o : Pt}
    (hSl : ∀ x∈rcbW S o++rcbR S p p,Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR S p p,x∈V)
    (hc : ScratchCT (ForwardField.programB M (dblJMul S p o)).inline) :
    RelCT isa (FieldPair M base size m Sl V E) (ForwardField.programB M (dblJMul S p o)).inline
      (FieldPair M base size m Sl ([o.x,o.y,o.z]++V) (runOps (dblJMul S p o) E)) := by
  have he : dblJMul S p o=ofN (dblJChoiceN true) S p p o := dblJChoice_eq true S p o
  rw [he] at hc ⊢
  exact ofN_forward_relCT hL hm (dblJChoiceN_ok true) hSl hV hc

end VG.Proof.Weierstrass.X86_64
