import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAdd

/-! Public-data mixed Jacobian addition retains a common field environment. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

structure JacMixedChecks (K : WinCfg) (p q o : Pt) : Prop where
  zero : ∀ a∈[p.z,K.S.t3,K.S.t5], FieldCT (.block (zeroMask K.M.n a))
  copyQ : FieldCT (.block (copyPt K.M.n o q))
  init : FieldCT (.block (copy K.M.n K.S.t2 p.x ++ copy K.M.n K.S.t4 p.y))
  head : FieldCT (fprogB K.M (jacMixedHead K.S p q))
  tail : FieldCT (fprogB K.M (jacMixedTail K.S p q o))
  double : FieldCT (fprogB K.M (dblJMul K.S p o))
  infinity : FieldCT (.block (Jacobian.infinity K o))

theorem jacMixedAdd_relCT {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hm : UnitMod m (2^(64*K.M.n))) {p q o : Pt} (hA : RcbApart K.S p q o)
    (hSl : ∀ x∈rcbW K.S o ++ rcbR K.S p q, Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR K.S p q, x∈V)
    (hOne : K.one<m) (hc : JacMixedChecks K p q o) :
    RelCT isa (FieldPair K.M base size m Sl V E) (Jacobian.jacMixedAdd K p q o)
      (fun s t => ∃ E', FieldPair K.M base size m Sl ([o.x,o.y,o.z]++V) E' s t) := by
  have os : ∀ x∈[o.x,o.y,o.z], Sl x := by
    intro x hx; apply hSl x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbW]
  have pv : ∀ x∈[p.x,p.y,p.z], x∈V := by
    intro x hx; apply hV x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbR]
  have qv : ∀ x∈[q.x,q.y,q.z], x∈V := by
    intro x hx; apply hV x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbR]
  rw [Jacobian.jacMixedAdd]
  apply fieldBranch_relCT hL hAl hm (pv _ (by simp)) (hc.zero _ (by simp))
  · intro _
    exact (copyPoint_relCT hL hAl os qv hc.copyQ).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
  · intro _
    have hi : RelCT isa (FieldPair K.M base size m Sl V E)
        (.block (copy K.M.n K.S.t2 p.x ++ copy K.M.n K.S.t4 p.y))
        (FieldPair K.M base size m Sl (K.S.t4::K.S.t2::V) (jacMixedInit K.S p E)) := by
      apply fieldWP_relCT hc.init
      intro s hs
      exact WP.mono (jacMixedInit_ok hL hAl hSl hs hV) fun _ ⟨hk,it⟩ => ⟨it,hk.sp⟩
    apply RelCT.seq hi
    have hh : RelCT isa (FieldPair K.M base size m Sl (K.S.t4::K.S.t2::V) (jacMixedInit K.S p E)) (fprogB K.M (jacMixedHead K.S p q))
        (FieldPair K.M base size m Sl (validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V)) (runOps (jacMixedHead K.S p q) (jacMixedInit K.S p E))) := by
      apply fieldWP_relCT hc.head
      intro s hi
      apply (fprogB_wp _ _).mpr
      exact WP.mono (jacMixedHead_ok hL hAl hm hA hSl hi hV) fun _ ⟨hk,it,_,_⟩ => ⟨it,hk.sp⟩
    apply RelCT.seq hh
    have oldV : ∀ x∈V, x∈validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V) :=
      fun x hx => (mem_validAfter _ _).mpr (Or.inl (by simp [hx]))
    have subV : ∀ x∈[o.x,o.y,o.z]++V, x∈[o.x,o.y,o.z]++validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V) := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (oldV x hx)
    apply fieldBranch_relCT hL hAl hm (a:=K.S.t3) (by
      rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out]) (hc.zero _ (by simp))
    · intro _
      apply fieldBranch_relCT hL hAl hm (a:=K.S.t5) (by
        rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out]) (hc.zero _ (by simp))
      · intro _
        have hdA : RcbApart K.S p p o := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
        have hdSl : ∀ x∈rcbW K.S o ++ rcbR K.S p p, Sl x := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hSl x (List.mem_append_left _ hx)
          · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
        have hv : ∀ x∈rcbR K.S p p, x∈validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V) :=
          fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
        have he := dblJChoice_eq true K.S p o
        have hd := ofN_relCT (base:=base) (E:=runOps (jacMixedHead K.S p q) (jacMixedInit K.S p E)) hL hAl hm (dblJChoiceN_ok true) hdA hdSl hv (by rw [←he]; exact hc.double)
        rw [←he] at hd
        exact hd.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
      · intro _
        exact (infinity_relCT hL hAl os hOne hc.infinity).mono
          (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
    · intro _
      have ht : RelCT isa
          (FieldPair K.M base size m Sl (validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V)) (runOps (jacMixedHead K.S p q) (jacMixedInit K.S p E)))
          (fprogB K.M (jacMixedTail K.S p q o))
          (FieldPair K.M base size m Sl ([o.x,o.y,o.z]++V)
            (runOps (jacMixedHead K.S p q ++ jacMixedTail K.S p q o) (jacMixedInit K.S p E))) := by
        apply fieldWP_relCT hc.tail
        intro s hi
        apply (fprogB_wp _ _).mpr
        exact WP.mono (jacMixedTail_ok hL hAl hm hA hSl hi hV) fun _ ⟨hk,it,_⟩ => ⟨it,hk.sp⟩
      exact ht.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)

end VG.Proof.Weierstrass.AArch64
