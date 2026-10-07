import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedForward
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointFieldTiming

/-! Mixed public addition recovers public flags from canonical field values. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

structure JacMixedChecks (K : WinCfg) (p q o : Pt) : Prop where
  zeroP : ScratchCT (.block (Jacobian.zeroTest K.M.n p.z))
  zeroH : ScratchCT (.block (Jacobian.zeroTest K.M.n K.S.t3))
  zeroR : ScratchCT (.block (Jacobian.zeroTest K.M.n K.S.t5))
  copyQ : ScratchCT (.block (copyPt K.M.n o q))
  init : ScratchCT (.block (copy K.M.n K.S.t2 p.x++copy K.M.n K.S.t4 p.y))
  head : ScratchCT (ForwardField.programB K.M (jacMixedHead K.S p q))
  tail : ScratchCT (ForwardField.programB K.M (jacMixedTail K.S p q o))
  double : ScratchCT (ForwardField.programB K.M (dblJMul K.S p o))
  infinity : ScratchCT (.block (Jacobian.infinity K o))

theorem jacMixedForward_relCT {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl)
    (hm : UnitMod m (2^(64*K.M.n))) {p q o : Pt}
    (hc : JacMixedChecks K p q o) (hA : RcbApart K.S p q o)
    (hSl : ∀ x∈rcbW K.S o++rcbR K.S p q,Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR K.S p q,x∈V) (hOne : K.one<m) :
    RelCT isa (FieldPair K.M base size m Sl V E)
      (Jacobian.jacMixedForward K p q o) (fun s t => ∃ E',FieldPair K.M base size m Sl ([o.x,o.y,o.z]++V) E' s t) := by
  have os : ∀ x∈[o.x,o.y,o.z],Sl x := by
    intro x hx
    apply hSl x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [rcbW]
  have qv : ∀ x∈[q.x,q.y,q.z],x∈V := by
    intro x hx
    apply hV x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [rcbR]
  rw [Jacobian.jacMixedForward]
  apply fieldBranch_relCT hL hm (hV p.z (by simp [rcbR])) hc.zeroP
  · intro _
    exact (copyPoint_relCT hL os qv hc.copyQ).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
  · intro _
    apply RelCT.seq (fieldProgram_relCT hc.init (fun s hi =>
      WP.mono (jacMixedInit_ok hL hSl hi hV) (fun _ ht => ht.2)))
    apply RelCT.seq (fieldProgram_relCT hc.head (fun s hi =>
      WP.mono (jacMixedForwardHead_ok hL hm hA hSl hi hV) (fun _ ht => ht.2.1)))
    have oldV : ∀ x∈V,x∈validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V) :=
      fun x hx => (mem_validAfter _ _).mpr (Or.inl (by simp [hx]))
    have subV : ∀ x∈[o.x,o.y,o.z]++V,x∈[o.x,o.y,o.z]++validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V) := by
      intro x hx
      rcases List.mem_append.mp hx with hx|hx
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (oldV x hx)
    apply fieldBranch_relCT hL hm (a:=K.S.t3) (by
      rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out]) hc.zeroH
    · intro _
      apply fieldBranch_relCT hL hm (a:=K.S.t5) (by
        rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out]) hc.zeroR
      · intro _
        have hdSl : ∀ x∈rcbW K.S o++rcbR K.S p p,Sl x := by
          intro x hx
          rcases List.mem_append.mp hx with hx|hx
          · exact hSl x (List.mem_append_left _ hx)
          · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
        have hdV : ∀ x∈rcbR K.S p p,x∈validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V) :=
          fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
        exact (doubleField_relCT hL hm hdSl hdV hc.double).mono
          (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
      · intro _
        exact (infinity_relCT hL os hOne hc.infinity).mono
          (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
    · intro _
      exact (fieldProgram_relCT hc.tail (fun s hi =>
        WP.mono (jacMixedForwardTail_ok hL hm hA hSl hi hV) (fun _ ht => ht.2.1))).mono
        (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)

end VG.Proof.Weierstrass.X86_64
