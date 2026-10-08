import VerifiedGarbage.Proof.P256.VerifyAllocated.Timing
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedArithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointMixedTiming

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

theorem mixedAdd_relCT (raw : RawCorrect) {base : Addr}
    (hm : UnitMod C.p (2^(64*K.M.n)))
    {V : List Nat} {E : Nat → Fe C} (hV : ∀ x∈rcbR K.S K.R K.E,x∈V)
    (hOne : K.one<C.p) (hc : JointMixedChecks K K.R K.E K.D) :
    RelCT isa (FieldPair K.M base 8192 C.p Sl V E)
      VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.mixedAdd
      (fun s t => ∃ E',FieldPair K.M base 8192 C.p Sl ([K.D.x,K.D.y,K.D.z]++V) E' s t) := by
  let hL := JointLayout.layout.lay
  let hAl := JointLayout.layout.aligned
  have hA : RcbApart K.S K.R K.E K.D := apart
  have hSl : ∀x∈rcbW K.S K.D++rcbR K.S K.R K.E,Sl x := by decide +kernel
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
  rw [VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.mixedAdd]
  apply fieldBranch_relCT hL hAl hm (pv K.R.z (by simp)) (hc.zero K.R.z (by simp))
  · intro _
    exact (copyPoint_relCT hL hAl os qv hc.copyQ).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
  · intro _
    have hi : RelCT isa (FieldPair K.M base 8192 C.p Sl V E)
        (.block (copy K.M.n K.S.t2 K.R.x ++ copy K.M.n K.S.t4 K.R.y))
        (FieldPair K.M base 8192 C.p Sl (K.S.t4::K.S.t2::V) (jacMixedInit K.S K.R E)) := by
      apply fieldWP_relCT hc.init
      intro s hs
      exact WP.mono (jacMixedInit_ok hL hAl hSl hs hV) fun _ ⟨hk,it⟩ => ⟨it,hk.sp⟩
    apply RelCT.seq hi
    have hh : RelCT isa (FieldPair K.M base 8192 C.p Sl (K.S.t4::K.S.t2::V) (jacMixedInit K.S K.R E)) (VG.Impl.P256.VerifyAllocated.program .mixedHead)
        (FieldPair K.M base 8192 C.p Sl (validAfter (jacMixedHead K.S K.R K.E) (K.S.t4::K.S.t2::V)) (runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E))) := by
      apply fieldWP_relCT Proof.P256.VerifyAllocated.MixedHead_ct
      intro s hi
      exact WP.mono (mixedHead_ok raw hi hV) fun _ ⟨hk,it,_,_⟩ => ⟨it,hk.regs.sp⟩
    apply RelCT.seq hh
    have oldV : ∀ x∈V, x∈validAfter (jacMixedHead K.S K.R K.E) (K.S.t4::K.S.t2::V) :=
      fun x hx => (mem_validAfter _ _).mpr (Or.inl (by simp [hx]))
    have subV : ∀ x∈[K.D.x,K.D.y,K.D.z]++V, x∈[K.D.x,K.D.y,K.D.z]++validAfter (jacMixedHead K.S K.R K.E) (K.S.t4::K.S.t2::V) := by
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
        have hdA : RcbApart K.S K.R K.R K.D := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
        have hdSl : ∀ x∈rcbW K.S K.D ++ rcbR K.S K.R K.R, Sl x := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hSl x (List.mem_append_left _ hx)
          · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
        have hv : ∀ x∈rcbR K.S K.R K.R, x∈validAfter (jacMixedHead K.S K.R K.E) (K.S.t4::K.S.t2::V) :=
          fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
        have hd := Forward.field_outputs_relCT Forward.Production.cases (base:=base) (E:=runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E)) hL hAl (callOf_small (by decide)) hm hdA hdSl hv hc.double
        exact hd.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
      · intro _
        exact (infinity_relCT hL hAl os hOne hc.infinity).mono
          (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
    · intro _
      have ht : RelCT isa
          (FieldPair K.M base 8192 C.p Sl (validAfter (jacMixedHead K.S K.R K.E) (K.S.t4::K.S.t2::V)) (runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E)))
          (VG.Impl.P256.VerifyAllocated.program .mixedTail)
          (FieldPair K.M base 8192 C.p Sl ([K.D.x,K.D.y,K.D.z]++V)
            (runOps (jacMixedHead K.S K.R K.E ++ jacMixedTail K.S K.R K.E K.D) (jacMixedInit K.S K.R E))) := by
        apply fieldWP_relCT Proof.P256.VerifyAllocated.MixedTail_ct
        intro s hi
        exact WP.mono (mixedTail_ok raw hi hV) fun _ ⟨hk,it,_⟩ => ⟨it,hk.regs.sp⟩
      exact ht.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)


end VG.Proof.Ecdsa.Verify.AArch64.Allocated
