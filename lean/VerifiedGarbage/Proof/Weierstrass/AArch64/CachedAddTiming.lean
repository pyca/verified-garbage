import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedAdd
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

structure Checks : Prop where
  zero : ∀ a∈[K.R.z,K.E.z,K.S.t3,K.S.t5], FieldCT (.block (zeroMask K.M.n a))
  copyP : FieldCT (.block (copyPt K.M.n K.D K.R))
  copyQ : FieldCT (.block (copyPt K.M.n K.D K.E))
  head : FieldCT ops.head
  tail : FieldCT ops.tail
  double : FieldCT ops.double
  infinity : FieldCT (.block (Jacobian.infinity K K.D))

/-- The complete addition's data-dependent branches inspect only field values
shared by the two executions. No condition on uninitialized scratch is needed. -/
theorem add_relCT {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hm : UnitMod m (2^(64*K.M.n))) (hsize : 8192≤size)
    (hSlots : ∀ x∈slots,Sl x)
    {V : List Nat} {E : Nat → Fin m} (hInputs : ∀ x∈inputs,x∈V)
    (hOne : K.one<m) (hc : Checks) :
    RelCT isa (FieldPair K.M base size m Sl V E) (CachedJac.add K ops)
      (fun s t => ∃ E', FieldPair K.M base size m Sl ([K.D.x,K.D.y,K.D.z]++V) E' s t) := by
  have hA : RcbApart K.S K.R K.E K.D := ⟨by decide +kernel,by decide +kernel⟩
  have hSl : ∀ x∈rcbW K.S K.D ++ rcbR K.S K.R K.E,Sl x := by
    intro x hx
    exact hSlots x (by simpa only [slots,inputs,List.append_assoc] using List.mem_append_left [5400,5432] hx)
  have hV : ∀ x∈rcbR K.S K.R K.E,x∈V := fun x hx => hInputs x (List.mem_append_left _ hx)
  have os : ∀ x∈[K.D.x,K.D.y,K.D.z], Sl x := by
    intro x hx; apply hSl x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbW]
  have pv : ∀ x∈[K.R.x,K.R.y,K.R.z], x∈V := by
    intro x hx; apply hV x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbR]
  have qv : ∀ x∈[K.E.x,K.E.y,K.E.z], x∈V := by
    intro x hx; apply hV x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbR]
  rw [CachedJac.add]
  apply fieldBranch_relCT hL hAl hm (pv _ (by simp)) (hc.zero _ (by simp))
  · intro _
    exact (copyPoint_relCT hL hAl os qv hc.copyQ).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
  · intro _
    apply fieldBranch_relCT hL hAl hm (qv _ (by simp)) (hc.zero _ (by simp))
    · intro _
      exact (copyPoint_relCT hL hAl os pv hc.copyP).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
    · intro _
      have hh : RelCT isa (FieldPair K.M base size m Sl V E) ops.head
          (FieldPair K.M base size m Sl (validAfter head V) (runOps head E)) := by
        dsimp only [ops]
        exact Forward.Arithmetic.field_relCT Forward.Arithmetic.cases hL hAl hm hsize head
          (fun op hop x hx => hSlots x (slots_head op hop x hx)) (readsOk_mono reads_head hInputs) (by simpa only [ops] using hc.head)
      apply RelCT.seq hh
      have oldV : ∀ x∈V, x∈validAfter head V :=
        fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
      have subV : ∀ x∈[K.D.x,K.D.y,K.D.z]++V, x∈[K.D.x,K.D.y,K.D.z]++validAfter head V := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_append_left _ hx
        · exact List.mem_append_right _ (oldV x hx)
      apply fieldBranch_relCT hL hAl hm (a:=K.S.t3) (by
        rw [mem_validAfter]; right; decide +kernel) (hc.zero _ (by simp))
      · intro _
        apply fieldBranch_relCT hL hAl hm (a:=K.S.t5) (by
          rw [mem_validAfter]; right; decide +kernel) (hc.zero _ (by simp))
        · intro _
          have hdA : RcbApart K.S K.R K.R K.D := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
          have hdSl : ∀ x∈rcbW K.S K.D ++ rcbR K.S K.R K.R, Sl x := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hSl x (List.mem_append_left _ hx)
            · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
          have hv : ∀ x∈rcbR K.S K.R K.R, x∈validAfter head V :=
            fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
          have hd := Forward.field_outputs_relCT Forward.Production.cases (base:=base) (E:=runOps head E) hL hAl hm hdA hdSl hv (by simpa only [ops] using hc.double)
          dsimp only [ops]
          exact hd.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
        · intro _
          exact (infinity_relCT hL hAl os hOne hc.infinity).mono
            (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
      · intro _
        have ht : RelCT isa
            (FieldPair K.M base size m Sl (validAfter head V) (runOps head E))
            ops.tail
            (FieldPair K.M base size m Sl ([K.D.x,K.D.y,K.D.z]++V)
              (runOps (head++tail) E)) := by
          have hr := readsOk_mono reads_full hInputs
          rw [readsOk_append,Bool.and_eq_true] at hr
          dsimp only [ops]
          have ht := Forward.Arithmetic.field_relCT Forward.Arithmetic.cases (base:=base)
            (E:=runOps head E) hL hAl hm hsize tail
            (fun op hop x hx => hSlots x (slots_tail op hop x hx)) hr.2 (by simpa only [ops] using hc.tail)
          rw [runOps_append]
          exact ht.mono (fun _ _ h => h) (fun _ _ h => h.sub (by
            intro x hx
            rw [mem_validAfter]
            rcases List.mem_append.mp hx with hx | hx
            · exact Or.inr (out_tail x hx)
            · exact Or.inl ((mem_validAfter _ _).mpr (Or.inl hx))))
        exact ht.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)

end VG.Proof.Weierstrass.AArch64.CachedField
