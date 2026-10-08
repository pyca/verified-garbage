import VerifiedGarbage.Proof.Weierstrass.X86.PointFieldTiming

/-! Ordinary Jacobian addition retains equal public field environments in every branch. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86

theorem doubleFieldPlain_relCT {counter : BitVec 32} {F : Spec.Weierstrass.Mont.Modulus} {wk : Nat} {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hW : WkOk F M m size wk Sl) (hm : UnitMod m (2^(64*M.n)))
    {S : RcbSlots} {p o : Pt} (hSl : ∀ x∈rcbW S o++rcbR S p p,Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR S p p,x∈V)
    (hc : ScratchCT (fprog F (dblJMul S p o))) :
    RelCT isa (FieldPair M base size m Sl V E counter) (fprog F (dblJMul S p o))
      (FieldPair M base size m Sl ([o.x,o.y,o.z]++V) (runOps (dblJMul S p o) E) counter) := by
  have he : dblJMul S p o=ofN (dblJChoiceN true) S p p o := dblJChoice_eq true S p o
  rw [he] at hc ⊢
  apply fieldProgram_relCT hc
  intro s hi
  refine WP.mono (fprog_ok hL hW hm _ hi
    (fun op hop x hx => hSl x (ofN_slots op hop x hx))
    (readsOk_mono (ofN_readsOk (dblJChoiceN_ok true) S p p o) hV)) fun _ ht => ⟨⟨ht.1.gpr,ht.1.rd,ht.1.wr⟩,ht.2.sub ?_⟩
  intro x hx
  rw [mem_validAfter]
  rcases List.mem_append.mp hx with hx|hx
  · exact Or.inr (ofN_out_mem (dblJChoiceN_ok true) hx)
  · exact Or.inl hx

structure JacAddChecks (K : WinCfg) (F : Spec.Weierstrass.Mont.Modulus) (p q o : Pt) : Prop where
  zeroP : ScratchCT (.block (Jacobian.zeroTest K.M.n p.z))
  zeroQ : ScratchCT (.block (Jacobian.zeroTest K.M.n q.z))
  zeroH : ScratchCT (.block (Jacobian.zeroTest K.M.n K.S.t3))
  zeroR : ScratchCT (.block (Jacobian.zeroTest K.M.n K.S.t5))
  copyP : ScratchCT (.block (copyPt K.M.n o p))
  copyQ : ScratchCT (.block (copyPt K.M.n o q))
  head : ScratchCT (fprog F (jacHead K.S p q))
  tail : ScratchCT (fprog F (jacTail K.S p q o))
  double : ScratchCT (fprog F (dblJMul K.S p o))
  infinity : ScratchCT (.block (Jacobian.infinity K o))

theorem jacAdd_relCT {counter : BitVec 32} {F : Spec.Weierstrass.Mont.Modulus} {wk : Nat} {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hW : WkOk F K.M m size wk Sl)
    (hm : UnitMod m (2^(64*K.M.n))) {p q o : Pt}
    (hc : JacAddChecks K F p q o) (hA : RcbApart K.S p q o)
    (hSl : ∀ x∈rcbW K.S o++rcbR K.S p q,Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR K.S p q,x∈V)
    (hOne : K.one<m) :
    RelCT isa (FieldPair K.M base size m Sl V E counter)
      (Jacobian.jacAdd K F p q o) (fun s t => ∃ E',FieldPair K.M base size m Sl ([o.x,o.y,o.z]++V) E' counter s t) := by
  have hs := hSl
  have hv := hV
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
  rw [Jacobian.jacAdd]
  apply fieldBranch_relCT hL hm (hV p.z (by simp [rcbR])) hc.zeroP
  · intro _
    exact (copyPoint_relCT hL hW os qv hc.copyQ).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
  · intro _
    apply fieldBranch_relCT hL hm (hV q.z (by simp [rcbR])) hc.zeroQ
    · intro _
      exact (copyPoint_relCT hL hW os pv hc.copyP).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
    · intro _
      apply RelCT.seq (fieldProgram_relCT hc.head (fun s hi =>
        WP.mono (jacHead_ok hL hW hm hA hSl hi hV)
          (fun _ ht => ⟨⟨ht.1.gpr,ht.1.rd,ht.1.wr⟩,ht.2.1⟩)))
      have oldV : ∀ x∈V,x∈validAfter (jacHead K.S p q) V :=
        fun x hx => (mem_validAfter _ _).mpr (Or.inl (by simp [hx]))
      have subV : ∀ x∈[o.x,o.y,o.z]++V,x∈[o.x,o.y,o.z]++validAfter (jacHead K.S p q) V := by
        intro x hx
        rcases List.mem_append.mp hx with hx|hx
        · exact List.mem_append_left _ hx
        · exact List.mem_append_right _ (oldV x hx)
      apply fieldBranch_relCT hL hm (a:=K.S.t3) (by
        rw [mem_validAfter]; right; simp [jacHead,FOp.out]) hc.zeroH
      · intro _
        apply fieldBranch_relCT hL hm (a:=K.S.t5) (by
          rw [mem_validAfter]; right; simp [jacHead,FOp.out]) hc.zeroR
        · intro _
          have hdSl : ∀ x∈rcbW K.S o++rcbR K.S p p,Sl x := by
            intro x hx
            rcases List.mem_append.mp hx with hx|hx
            · exact hs x (List.mem_append_left _ hx)
            · exact hs x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
          have hdV : ∀ x∈rcbR K.S p p,x∈validAfter (jacHead K.S p q) V :=
            fun x hx => oldV x (hv x (rcbR_self_mem _ _ _ hx))
          exact (doubleFieldPlain_relCT hL hW hm hdSl hdV hc.double).mono
            (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
        · intro _
          exact (infinity_relCT hL hW os hOne hc.infinity).mono
            (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
      · intro _
        exact (fieldProgram_relCT hc.tail (fun s hi =>
          WP.mono (jacTail_ok hL hW hm hA hSl hi hV) (fun _ ht => ⟨⟨ht.1.gpr,ht.1.rd,ht.1.wr⟩,ht.2.1⟩))).mono
          (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)

end VG.Proof.Weierstrass.X86
