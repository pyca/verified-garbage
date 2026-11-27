module
public import VerifiedGarbage.Proof.Weierstrass.JacMul
public import VerifiedGarbage.Impl.Weierstrass.X86_64.JacMixedForward
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming

public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedForward
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointFieldTiming
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedAdd

/-! Mixed public addition recovers public flags from canonical field values. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

/-- The checks of `CachedJac.addEnd`'s parts, its doubling `dbl`. -/
structure AddEndChecks (K : WinCfg) (p q o : Pt) (dbl : RcbSlots → Pt → Pt → List FOp := dblJMul) : Prop where
  zeroH : ScratchCT (.block (Jacobian.zeroTest K.M.n K.S.t3))
  zeroR : ScratchCT (.block (Jacobian.zeroTest K.M.n K.S.t5))
  tail : ScratchCT (ForwardField.programB K.M (jacEndTail K.S p q o)).inline
  double : ScratchCT (ForwardField.programB K.M (dbl K.S p o)).inline
  infinity : ScratchCT (.block (Jacobian.infinity K o))

/-- The end of the additions, from any slots `W` holding what it reads. -/
theorem addEnd_relCT {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl)
    (hm : UnitMod m (2^(64*K.M.n))) {p q o : Pt} {dbl : RcbSlots → Pt → Pt → List FOp}
    (hc : AddEndChecks K p q o dbl)
    (hSl : ∀ x∈rcbW K.S o++rcbR K.S p q,Sl x)
    {W : List Nat} {E : Nat → Fin m} (hW : ∀ x ∈ endIns K.S o, x ∈ W) (hpW : ∀ x∈rcbR K.S p p,x∈W)
    (hOne : K.one<m) (hds : JDblShape dbl) :
    RelCT isa (FieldPair K.M base size m Sl W E)
      (CachedJac.addEnd K p q o dbl).inline (fun s t => ∃ E',FieldPair K.M base size m Sl ([o.x,o.y,o.z]++W) E' s t) := by
  have os : ∀ x∈[o.x,o.y,o.z],Sl x := by
    intro x hx
    apply hSl x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [rcbW]
  rw [CachedJac.addEnd]
  apply fieldBranch_relCT hL hm (hW K.S.t3 (by simp)) hc.zeroH
  · intro _
    apply fieldBranch_relCT hL hm (hW K.S.t5 (by simp)) hc.zeroR
    · intro _
      have hdSl : ∀ x∈rcbW K.S o++rcbR K.S p p,Sl x := by
        intro x hx
        rcases List.mem_append.mp hx with hx|hx
        · exact hSl x (List.mem_append_left _ hx)
        · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
      exact (doubleField_relCT hL hm hdSl hpW hds hc.double).mono
        (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
    · intro _
      exact (infinity_relCT hL os hOne hc.infinity).mono
        (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
  · intro _
    exact (fieldProgram_relCT hc.tail (fun s hi =>
      WP.mono (endTail_ok hL hm hSl hi hW) (fun _ ht => ht.2))).mono
      (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)

/-- The checks of `Jacobian.jacMixedForward`'s parts, its doubling `dbl`. -/
structure JacMixedChecks (K : WinCfg) (p q o : Pt) (dbl : RcbSlots → Pt → Pt → List FOp := dblJMul) : Prop where
  zeroP : ScratchCT (.block (Jacobian.zeroTest K.M.n p.z))
  zeroH : ScratchCT (.block (Jacobian.zeroTest K.M.n K.S.t3))
  zeroR : ScratchCT (.block (Jacobian.zeroTest K.M.n K.S.t5))
  copyQ : ScratchCT (.block (copyPt K.M.n o q))
  init : ScratchCT (.block (copy K.M.n K.S.t2 p.x++copy K.M.n K.S.t4 p.y++copy K.M.n o.z p.z))
  head : ScratchCT (ForwardField.programB K.M (jacMixedHead K.S p q)).inline
  tail : ScratchCT (ForwardField.programB K.M (jacEndTail K.S p q o)).inline
  double : ScratchCT (ForwardField.programB K.M (dbl K.S p o)).inline
  infinity : ScratchCT (.block (Jacobian.infinity K o))

theorem JacMixedChecks.fin {K : WinCfg} {p q o : Pt} {dbl : RcbSlots → Pt → Pt → List FOp}
    (h : JacMixedChecks K p q o dbl) : AddEndChecks K p q o dbl :=
  ⟨h.zeroH, h.zeroR, h.tail, h.double, h.infinity⟩

theorem jacMixedForward_relCT {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl)
    (hm : UnitMod m (2^(64*K.M.n))) {p q o : Pt} {dbl : RcbSlots → Pt → Pt → List FOp}
    (hc : JacMixedChecks K p q o dbl) (hA : RcbApart K.S p q o)
    (hSl : ∀ x∈rcbW K.S o++rcbR K.S p q,Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR K.S p q,x∈V) (hOne : K.one<m) (hds : JDblShape dbl := by exact jdblShape_dblJMul) :
    RelCT isa (FieldPair K.M base size m Sl V E)
      (Jacobian.jacMixedForward K p q o dbl).inline (fun s t => ∃ E',FieldPair K.M base size m Sl ([o.x,o.y,o.z]++V) E' s t) := by
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
      WP.mono (jacMixedInitZ_ok hL hSl hi hV) (fun _ ht => ht.2)))
    apply RelCT.seq (fieldProgram_relCT hc.head (fun s hi =>
      WP.mono (jacMixedForwardHead_ok hL hm hA hSl hi hV) (fun _ ht => ht.2.1)))
    have oldV : ∀ x∈V,x∈validAfter (jacMixedHead K.S p q) (o.z::K.S.t4::K.S.t2::V) :=
      fun x hx => (mem_validAfter _ _).mpr (Or.inl (by simp [hx]))
    have subV : ∀ x∈[o.x,o.y,o.z]++V,x∈[o.x,o.y,o.z]++validAfter (jacMixedHead K.S p q) (o.z::K.S.t4::K.S.t2::V) := by
      intro x hx
      rcases List.mem_append.mp hx with hx|hx
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (oldV x hx)
    have hW : ∀ x ∈ endIns K.S o, x ∈ validAfter (jacMixedHead K.S p q) (o.z::K.S.t4::K.S.t2::V) := by
      intro x hx
      rw [mem_validAfter]
      simp only [endIns,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [jacMixedHead,FOp.out]
    exact (addEnd_relCT hL hm hc.fin hSl hW (fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))) hOne hds).mono
      (fun _ _ h => h) (fun _ _ ⟨_,h⟩ => ⟨_,h.sub subV⟩)

end VG.Proof.Weierstrass.X86_64
