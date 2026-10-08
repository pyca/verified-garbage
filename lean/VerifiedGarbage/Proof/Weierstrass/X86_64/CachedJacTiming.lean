import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacOps
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointFieldTiming

/-! Cached public addition: fixed-address pieces and equal public branch conditions. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

structure CachedJacChecks (K : WinCfg) (p q o : Pt) (dst : Nat) : Prop where
  zeroP : ScratchCT (.block (Jacobian.zeroTest K.M.n p.z))
  zeroQ : ScratchCT (.block (Jacobian.zeroTest K.M.n q.z))
  zeroH : ScratchCT (.block (Jacobian.zeroTest K.M.n K.S.t3))
  zeroR : ScratchCT (.block (Jacobian.zeroTest K.M.n K.S.t5))
  copyP : ScratchCT (.block (copyPt K.M.n o p))
  copyQ : ScratchCT (.block (copyPt K.M.n o q))
  head : ScratchCT (ForwardField.programB K.M (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S p q dst)).inline
  tail : ScratchCT (ForwardField.programB K.M (jacTail K.S p q o)).inline
  double : ScratchCT (ForwardField.programB K.M (dblJMul K.S p o)).inline
  infinity : ScratchCT (.block (Jacobian.infinity K o))

theorem cachedJacAdd_relCT {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl)
    (hm : UnitMod m (2^(64*K.M.n))) {p q o : Pt} {dst : Nat}
    (hc : CachedJacChecks K p q o dst) (hA : RcbApart K.S p q o)
    (h2a : dst∉rcbW K.S o) (h3a : dst+8*K.M.n∉rcbW K.S o)
    (hSl : ∀ x∈(rcbW K.S o++rcbR K.S p q)++[dst,dst+8*K.M.n],Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR K.S p q++[dst,dst+8*K.M.n],x∈V)
    (hOne : K.one<m)
    (h2 : E dst=E q.z*E q.z) (h3 : E (dst+8*K.M.n)=E dst*E q.z) :
    RelCT isa (FieldPair K.M base size m Sl V E)
      (Impl.Weierstrass.X86_64.CachedJac.add K p q o dst).inline (fun s t => ∃ E',FieldPair K.M base size m Sl ([o.x,o.y,o.z]++V) E' s t) := by
  have hs : ∀ x∈rcbW K.S o++rcbR K.S p q,Sl x := fun x hx => hSl x (List.mem_append_left _ hx)
  have hv : ∀ x∈rcbR K.S p q,x∈V := fun x hx => hV x (List.mem_append_left _ hx)
  have os : ∀ x∈[o.x,o.y,o.z],Sl x := by
    intro x hx
    apply hs x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [rcbW]
  have qv : ∀ x∈[q.x,q.y,q.z],x∈V := by
    intro x hx
    apply hv x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [rcbR]
  have pv : ∀ x∈[p.x,p.y,p.z],x∈V := by
    intro x hx
    apply hv x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [rcbR]
  rw [Impl.Weierstrass.X86_64.CachedJac.add]
  apply fieldBranch_relCT hL hm (hV p.z (by simp [rcbR])) hc.zeroP
  · intro _
    exact (copyPoint_relCT hL os qv hc.copyQ).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
  · intro _
    apply fieldBranch_relCT hL hm (hV q.z (by simp [rcbR])) hc.zeroQ
    · intro _
      exact (copyPoint_relCT hL os pv hc.copyP).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
    · intro _
      apply RelCT.seq (fieldProgram_relCT hc.head (fun s hi =>
        WP.mono (CachedJac.head_ok hL hm hA h2a h3a hSl hi hV h2 h3)
          (fun _ ht => ht.2.1)))
      have oldV : ∀ x∈V,x∈validAfter (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S p q dst) V :=
        fun x hx => (mem_validAfter _ _).mpr (Or.inl (by simp [hx]))
      have subV : ∀ x∈[o.x,o.y,o.z]++V,x∈[o.x,o.y,o.z]++validAfter (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S p q dst) V := by
        intro x hx
        rcases List.mem_append.mp hx with hx|hx
        · exact List.mem_append_left _ hx
        · exact List.mem_append_right _ (oldV x hx)
      apply fieldBranch_relCT hL hm (a:=K.S.t3) (by
        rw [mem_validAfter]; right; simp [Impl.Weierstrass.X86_64.CachedJac.head,FOp.out]) hc.zeroH
      · intro _
        apply fieldBranch_relCT hL hm (a:=K.S.t5) (by
          rw [mem_validAfter]; right; simp [Impl.Weierstrass.X86_64.CachedJac.head,FOp.out]) hc.zeroR
        · intro _
          have hdSl : ∀ x∈rcbW K.S o++rcbR K.S p p,Sl x := by
            intro x hx
            rcases List.mem_append.mp hx with hx|hx
            · exact hs x (List.mem_append_left _ hx)
            · exact hs x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
          have hdV : ∀ x∈rcbR K.S p p,x∈validAfter (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S p q dst) V :=
            fun x hx => oldV x (hv x (rcbR_self_mem _ _ _ hx))
          exact (doubleField_relCT hL hm hdSl hdV hc.double).mono
            (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
        · intro _
          exact (infinity_relCT hL os hOne hc.infinity).mono
            (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
      · intro _
        exact (fieldProgram_relCT hc.tail (fun s hi =>
          WP.mono (CachedJac.tail_ok hL hm hA h2a h3a hSl hi hV h2 h3) (fun _ ht => ht.2.1))).mono
          (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)

end VG.Proof.Weierstrass.X86_64
