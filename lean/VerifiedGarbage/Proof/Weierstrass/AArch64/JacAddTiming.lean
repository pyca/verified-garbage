import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Production
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Timing
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming

/-! Exceptional branches on public Jacobian coordinates preserve a shared,
exact field environment, including the infinity and point-copy branches. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

abbrev FieldCT (c : Prog isa) :=
  ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) c

def copyPointEnv {F : Type _} (E : Nat → F) (o q : Pt) : Nat → F :=
  let e₁ := Function.update E o.x (E q.x)
  let e₂ := Function.update e₁ o.y (e₁ q.y)
  Function.update e₂ o.z (e₂ q.z)

theorem copyPoint_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    {o q : Pt} (hSl : ∀ x∈[o.x,o.y,o.z], Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈[q.x,q.y,q.z], x∈V)
    (hct : FieldCT (.block (copyPt M.n o q))) :
    RelCT isa (FieldPair M base size m Sl V E) (.block (copyPt M.n o q))
      (FieldPair M base size m Sl ([o.x,o.y,o.z]++V) (copyPointEnv E o q)) := by
  apply fieldWP_relCT hct
  intro s hi
  rw [copyPt,List.append_assoc,WP.block_append_iff]
  refine WP.mono (copyField_ok hL hAl hi (hSl _ (by simp)) (hV _ (by simp))) fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok hL hAl ia (hSl _ (by simp))
    (List.mem_cons_of_mem _ (hV _ (by simp)))) fun b ⟨kb,ib⟩ => ?_
  refine WP.mono (copyField_ok hL hAl ib (hSl _ (by simp))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hV _ (by simp))))) fun t ⟨kt,it⟩ => ?_
  refine ⟨it.sub ?_,kt.sp.trans (kb.sp.trans ka.sp)⟩
  intro x hx
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

def infinityEnv (M : Mod) (m one : Nat) [NeZero m] (E : Nat → Fin m) (o : Pt) : Nat → Fin m :=
  Function.update (Function.update (Function.update E o.x (toM m (2^(64*M.n)) 0))
    o.y (toM m (2^(64*M.n)) one)) o.z (toM m (2^(64*M.n)) 0)

theorem infinity_relCT {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    {o : Pt} (hSl : ∀ x∈[o.x,o.y,o.z], Sl x) (hOne : K.one<m)
    {V : List Nat} {E : Nat → Fin m} (hct : FieldCT (.block (Jacobian.infinity K o))) :
    RelCT isa (FieldPair K.M base size m Sl V E) (.block (Jacobian.infinity K o))
      (FieldPair K.M base size m Sl ([o.x,o.y,o.z]++V) (infinityEnv K.M m K.one E o)) := by
  apply fieldWP_relCT hct
  intro s hi
  have hR := wordsVal_lt s.mem base K.M.mo K.M.n
  rw [hi.mod.val] at hR
  have h0 : 0<m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [Jacobian.infinity,List.append_assoc,WP.block_append_iff]
  refine WP.mono (setField_ok hL hAl hi (hSl _ (by simp)) h0 hR) fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setField_ok hL hAl ia (hSl _ (by simp)) hOne hR) fun b ⟨kb,ib⟩ => ?_
  refine WP.mono (setField_ok hL hAl ib (hSl _ (by simp)) h0 hR) fun t ⟨kt,it⟩ => ?_
  refine ⟨it.sub ?_,kt.sp.trans (kb.sp.trans ka.sp)⟩
  intro x hx
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

/-- The straight-line pieces are checked once for the concrete configuration. -/
structure JacAddChecks (K : WinCfg) (p q o : Pt) : Prop where
  zero : ∀ a∈[p.z,q.z,K.S.t3,K.S.t5], FieldCT (.block (zeroMask K.M.n a))
  copyP : FieldCT (.block (copyPt K.M.n o p))
  copyQ : FieldCT (.block (copyPt K.M.n o q))
  head : FieldCT (fprogB K.M (jacHead K.S p q))
  tail : FieldCT (fprogB K.M (jacTail K.S p q o))
  double : FieldCT (VG.Impl.P256.VerifyDouble.double K.M K.S p o)
  infinity : FieldCT (.block (Jacobian.infinity K o))

/-- Numbered field arithmetic preserves an exact environment in both runs. -/
theorem ofN_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl) (hnc : Mont.callOf M = none)
    (hm : UnitMod m (2^(64*M.n))) {N : List FOp} (hN : NumOk N)
    {S : RcbSlots} {p q o : Pt} (hA : RcbApart S p q o)
    (hSl : ∀ x∈rcbW S o ++ rcbR S p q, Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR S p q, x∈V)
    (hct : FieldCT (fprogB M (ofN N S p q o))) :
    RelCT isa (FieldPair M base size m Sl V E) (fprogB M (ofN N S p q o))
      (FieldPair M base size m Sl ([o.x,o.y,o.z]++V) (runOps (ofN N S p q o) E)) := by
  apply fieldWP_relCT hct
  intro s hi
  exact WP.mono (ofN_ok hL hAl hm hN hA hSl (.inl hnc) hi hV) fun _ ⟨hk,it,_⟩ => ⟨it,hk.sp⟩

/-- The complete addition's data-dependent branches inspect only field values
shared by the two executions. No condition on uninitialized scratch is needed. -/
theorem jacAdd_relCT {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hnc : Mont.callOf K.M = none)
    (hm : UnitMod m (2^(64*K.M.n))) {p q o : Pt} (hA : RcbApart K.S p q o)
    (hSl : ∀ x∈rcbW K.S o ++ rcbR K.S p q, Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR K.S p q, x∈V)
    (hOne : K.one<m) (hc : JacAddChecks K p q o) :
    RelCT isa (FieldPair K.M base size m Sl V E) (Jacobian.jacAdd K p q o)
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
  rw [Jacobian.jacAdd]
  apply fieldBranch_relCT hL hAl hm (pv _ (by simp)) (hc.zero _ (by simp))
  · intro _
    exact (copyPoint_relCT hL hAl os qv hc.copyQ).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
  · intro _
    apply fieldBranch_relCT hL hAl hm (qv _ (by simp)) (hc.zero _ (by simp))
    · intro _
      exact (copyPoint_relCT hL hAl os pv hc.copyP).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
    · intro _
      have hh : RelCT isa (FieldPair K.M base size m Sl V E) (fprogB K.M (jacHead K.S p q))
          (FieldPair K.M base size m Sl (validAfter (jacHead K.S p q) V) (runOps (jacHead K.S p q) E)) := by
        apply fieldWP_relCT hc.head
        intro s hi
        apply (fprogB_wp _ _ hnc).mpr
        exact WP.mono (jacHead_ok hL hAl hm hA hSl hi hV) fun _ ⟨hk,it,_,_⟩ => ⟨it,hk.sp⟩
      apply RelCT.seq hh
      have oldV : ∀ x∈V, x∈validAfter (jacHead K.S p q) V :=
        fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
      have subV : ∀ x∈[o.x,o.y,o.z]++V, x∈[o.x,o.y,o.z]++validAfter (jacHead K.S p q) V := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_append_left _ hx
        · exact List.mem_append_right _ (oldV x hx)
      apply fieldBranch_relCT hL hAl hm (a:=K.S.t3) (by
        rw [mem_validAfter]; right; simp [jacHead,FOp.out]) (hc.zero _ (by simp))
      · intro _
        apply fieldBranch_relCT hL hAl hm (a:=K.S.t5) (by
          rw [mem_validAfter]; right; simp [jacHead,FOp.out]) (hc.zero _ (by simp))
        · intro _
          have hdA : RcbApart K.S p p o := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
          have hdSl : ∀ x∈rcbW K.S o ++ rcbR K.S p p, Sl x := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hSl x (List.mem_append_left _ hx)
            · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
          have hv : ∀ x∈rcbR K.S p p, x∈validAfter (jacHead K.S p q) V :=
            fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
          have hd := Forward.field_outputs_relCT Forward.Production.cases (base:=base) (E:=runOps (jacHead K.S p q) E) hL hAl hnc hm hdA hdSl hv hc.double
          exact hd.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
        · intro _
          exact (infinity_relCT hL hAl os hOne hc.infinity).mono
            (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
      · intro _
        have ht : RelCT isa
            (FieldPair K.M base size m Sl (validAfter (jacHead K.S p q) V) (runOps (jacHead K.S p q) E))
            (fprogB K.M (jacTail K.S p q o))
            (FieldPair K.M base size m Sl ([o.x,o.y,o.z]++V)
              (runOps (jacHead K.S p q ++ jacTail K.S p q o) E)) := by
          apply fieldWP_relCT hc.tail
          intro s hi
          apply (fprogB_wp _ _ hnc).mpr
          exact WP.mono (jacTail_ok hL hAl hm hA hSl hi hV) fun _ ⟨hk,it,_⟩ => ⟨it,hk.sp⟩
        exact ht.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)

end VG.Proof.Weierstrass.AArch64
