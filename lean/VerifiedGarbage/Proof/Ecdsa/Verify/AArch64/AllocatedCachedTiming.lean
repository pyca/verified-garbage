import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFieldTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedAddTiming

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open CachedField

theorem cachedAdd_relCT (raw : RawCorrect) {base : Addr}
    (hm : UnitMod C.p (2^(64*K.M.n)))
    {V : List Nat} {E : Nat → Fe C} (hInputs : ∀ x∈CachedField.inputs,x∈V)
    (hOne : K.one<C.p) (hc : CachedField.Checks) :
    RelCT isa (FieldPair K.M base 8192 C.p Sl V E)
      (CachedJac.add K VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.cachedOps)
      (fun s t => ∃ E', FieldPair K.M base 8192 C.p Sl ([K.D.x,K.D.y,K.D.z]++V) E' s t) := by
  let hL := JointLayout.layout.lay
  let hAl := JointLayout.layout.aligned
  have ke : K=CachedField.K := rfl
  have hA : RcbApart K.S K.R K.E K.D := ⟨by decide,by decide⟩
  have hSl : ∀x∈rcbW K.S K.D++rcbR K.S K.R K.E,Sl x := by decide +kernel
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
  apply fieldBranch_relCT hL hAl hm (pv _ (by simp)) (hc.zero _ (by decide))
  · intro _
    exact (copyPoint_relCT hL hAl os qv hc.copyQ).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
  · intro _
    apply fieldBranch_relCT hL hAl hm (qv _ (by simp)) (hc.zero _ (by decide))
    · intro _
      exact (copyPoint_relCT hL hAl os pv hc.copyP).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
    · intro _
      have hh : RelCT isa (FieldPair K.M base 8192 C.p Sl V E) VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.cachedOps.head
          (FieldPair K.M base 8192 C.p Sl (validAfter head V) (runOps head E)) := by
        dsimp only [VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.cachedOps]
        exact field_all_relCT raw Proof.P256.VerifyAllocated.CachedHead.caseProof (by decide)
          (by decide +kernel) (readsOk_mono reads_head hInputs) Proof.P256.VerifyAllocated.CachedHead_ct
      apply RelCT.seq hh
      have oldV : ∀ x∈V, x∈validAfter head V :=
        fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
      have subV : ∀ x∈[K.D.x,K.D.y,K.D.z]++V, x∈[K.D.x,K.D.y,K.D.z]++validAfter head V := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_append_left _ hx
        · exact List.mem_append_right _ (oldV x hx)
      apply fieldBranch_relCT hL hAl hm (a:=K.S.t3) (by
        rw [mem_validAfter]; right; decide +kernel) (hc.zero _ (by decide))
      · intro _
        apply fieldBranch_relCT hL hAl hm (a:=K.S.t5) (by
          rw [mem_validAfter]; right; decide +kernel) (hc.zero _ (by decide))
        · intro _
          have hdA : RcbApart K.S K.R K.R K.D := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
          have hdSl : ∀ x∈rcbW K.S K.D ++ rcbR K.S K.R K.R, Sl x := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hSl x (List.mem_append_left _ hx)
            · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
          have hv : ∀ x∈rcbR K.S K.R K.R, x∈validAfter head V :=
            fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
          have hd := Forward.field_outputs_relCT Forward.Production.cases (base:=base) (E:=runOps head E) hL hAl hm hdA hdSl hv (by
            change FieldCT (VG.Impl.P256.VerifyDouble.double K.M K.S K.R K.D)
            rw [ke]
            simpa only [CachedField.ops] using hc.double)
          dsimp only [VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.cachedOps,VG.Impl.Ecdsa.Verify.AArch64.P256Joint.cachedOps]
          exact hd.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
        · intro _
          exact (infinity_relCT hL hAl os hOne hc.infinity).mono
            (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
      · intro _
        have ht : RelCT isa
            (FieldPair K.M base 8192 C.p Sl (validAfter head V) (runOps head E))
            VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.cachedOps.tail
            (FieldPair K.M base 8192 C.p Sl ([K.D.x,K.D.y,K.D.z]++V)
              (runOps (head++tail) E)) := by
          have hr := readsOk_mono reads_full hInputs
          rw [readsOk_append,Bool.and_eq_true] at hr
          dsimp only [VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.cachedOps]
          have ht := field_all_relCT raw Proof.P256.VerifyAllocated.JacTail.caseProof (by decide)
            (base:=base) (E:=runOps head E) (by decide +kernel) hr.2 Proof.P256.VerifyAllocated.JacTail_ct
          rw [runOps_append]
          exact ht.mono (fun _ _ h => h) (fun _ _ h => h.sub (by
            intro x hx
            rw [mem_validAfter]
            rcases List.mem_append.mp hx with hx | hx
            · exact Or.inr (out_tail x hx)
            · exact Or.inl ((mem_validAfter _ _).mpr (Or.inl hx))))
        exact ht.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)


end VG.Proof.Ecdsa.Verify.AArch64.Allocated
