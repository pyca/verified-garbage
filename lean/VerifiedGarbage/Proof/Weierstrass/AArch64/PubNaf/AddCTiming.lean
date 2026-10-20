module
public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNaf
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming

import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddC
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Add
import VerifiedGarbage.Proof.Weierstrass.JacMul

/-!
# Timing of the cached addition

`addCB_relCT` is `jacAddB_relCT` for `PubNaf.addC`, whose head reads `q`'s
`Z²` and `Z³` from `o.y` and `o.z`: two runs from the same values leak the
same trace.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

/-- The pieces of the cached addition whose timing taint tracking checks. -/
structure AddCChecks (K : WinCfg) (p q o : Pt) : Prop where
  zero : ∀ a∈[p.z,q.z,K.S.t3,K.S.t5], FieldCT (.block (zeroMask K.M.n a))
  copyP : FieldCT (.block (copyPt K.M.n o p))
  copyQ : FieldCT (.block (copyPt K.M.n o q))
  head : FieldCT (fprogB K.M (CachedJac.headAt K.S p q o.y o.z))
  tail : FieldCT (fprogB K.M (jacTail K.S p q o))
  double : FieldCT (VG.Impl.P256.VerifyDouble.double K.M K.S p o)
  infinity : FieldCT (.block (Jacobian.infinity K o))

theorem addCB_relCT {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hn4 : K.M.n ≠ 4)
    (hm : UnitMod m (2^(64*K.M.n))) {p q o : Pt} (hA : RcbApart K.S p q o)
    (hSl : ∀ x∈rcbW K.S o ++ rcbR K.S p q, Sl x) (hLow : Low K.M (rcbW K.S o ++ rcbR K.S p q))
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR K.S p q, x∈V) (hy : o.y ∈ V) (hz : o.z ∈ V)
    (h2 : E o.y = E q.z * E q.z) (h3 : E o.z = E q.z * (E q.z * E q.z))
    (hOne : K.one<m) (hc : AddCChecks K p q o) :
    RelCT isa (FieldPair K.M base size m Sl V E) (PubNaf.addC K p q o)
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
  rw [PubNaf.addC]
  apply fieldBranch_relCT hL hAl hm (pv _ (by simp)) (hc.zero _ (by simp))
  · intro _
    exact (copyPoint_relCT hL hAl os qv hc.copyQ).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
  · intro _
    apply fieldBranch_relCT hL hAl hm (qv _ (by simp)) (hc.zero _ (by simp))
    · intro _
      exact (copyPoint_relCT hL hAl os pv hc.copyP).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
    · intro _
      let H := CachedJac.headAt K.S p q o.y o.z
      have hh : RelCT isa (FieldPair K.M base size m Sl V E) (fprogB K.M H)
          (FieldPair K.M base size m Sl (validAfter H V) (runOps H E)) := by
        apply fieldWP_relCT hc.head
        intro s hi
        exact WP.mono (jacHeadCB_ok hL hAl hm hA hSl hLow hi hV hy hz h2 h3) fun _ ⟨hk,it,_,_⟩ => ⟨it,hk.sp⟩
      apply RelCT.seq hh
      have oldV : ∀ x∈V, x∈validAfter H V :=
        fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
      have subV : ∀ x∈[o.x,o.y,o.z]++V, x∈[o.x,o.y,o.z]++validAfter H V := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_append_left _ hx
        · exact List.mem_append_right _ (oldV x hx)
      apply fieldBranch_relCT hL hAl hm (a:=K.S.t3) (by
        rw [mem_validAfter]; right; simp [H, CachedJac.headAt, FOp.out]) (hc.zero _ (by simp))
      · intro _
        apply fieldBranch_relCT hL hAl hm (a:=K.S.t5) (by
          rw [mem_validAfter]; right; simp [H, CachedJac.headAt, FOp.out]) (hc.zero _ (by simp))
        · intro _
          have hdA : RcbApart K.S p p o := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
          have hsub : ∀ x ∈ rcbW K.S o ++ rcbR K.S p p, x ∈ rcbW K.S o ++ rcbR K.S p q := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact List.mem_append_left _ hx
            · exact List.mem_append_right _ (rcbR_self_mem _ _ _ hx)
          have hv : ∀ x∈rcbR K.S p p, x∈validAfter H V :=
            fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
          have e : dblJMul K.S p o = ofN (dblJChoiceN true) K.S p p o := dblJChoice_eq true K.S p o
          have hdc := hc.double
          rw [verifyDouble_eq hn4, e] at hdc
          rw [verifyDouble_eq hn4, e]
          have hd := ofNB_relCT (base := base) (E := runOps H E) hL hAl hm
            (dblJChoiceN_ok true) hdA (fun x hx => hSl x (hsub x hx)) (hLow.mono hsub) hv hdc
          exact hd.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
        · intro _
          exact (infinity_relCT hL hAl os hOne hc.infinity).mono
            (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
      · intro _
        have ht : RelCT isa
            (FieldPair K.M base size m Sl (validAfter H V) (runOps H E))
            (fprogB K.M (jacTail K.S p q o))
            (FieldPair K.M base size m Sl ([o.x,o.y,o.z]++V) (runOps (H ++ jacTail K.S p q o) E)) := by
          apply fieldWP_relCT hc.tail
          intro s hi
          exact WP.mono (jacTailCB_ok hL hAl hm hA hSl hLow hi hV hy hz h2 h3) fun _ ⟨hk,it,_⟩ => ⟨it,hk.sp⟩
        exact ht.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)

end VG.Proof.Weierstrass.AArch64
