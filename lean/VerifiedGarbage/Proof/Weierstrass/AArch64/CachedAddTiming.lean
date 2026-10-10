import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedField
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming

/-! ## `CachedAddField` -/

section

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64

def inputs : List Nat := rcbR K.S K.R K.E ++ [5400,5432]
def slots : List Nat := rcbW K.S K.D ++ inputs

def ops : CachedJac.Ops where
  head := VG.Impl.P256.VerifyArithmetic.program K.M head
  tail := VG.Impl.P256.VerifyArithmetic.program K.M tail
  double := VG.Impl.P256.VerifyDouble.double K.M K.S K.R K.D

theorem slots_head : ∀ op∈head,∀ x∈op.out::op.ins,x∈slots := by decide +kernel
theorem slots_tail : ∀ op∈tail,∀ x∈op.out::op.ins,x∈slots := by decide +kernel
theorem writes_head : ∀ op∈head,op.out∈rcbW K.S K.D := by decide +kernel
theorem writes_tail : ∀ op∈tail,op.out∈rcbW K.S K.D := by decide +kernel
theorem out_tail : ∀ x∈[K.D.x,K.D.y,K.D.z],x∈tail.map FOp.out := by decide +kernel
theorem reads_head : readsOk head inputs=true := by decide +kernel
theorem reads_full : readsOk (head++tail) inputs=true := by decide +kernel

theorem head_readonly {F : Type} [Lean.Grind.CommRing F] (E : Nat → F)
    {x : Nat} (hx : x∈inputs) : runOps head E x=E x := by
  apply runOps_of_not_out
  have h : ∀ op∈head,∀ x∈inputs,op.out≠x := by decide +kernel
  exact fun op hop => h op hop x hx

theorem head_ok {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hm : UnitMod m (2^(64*K.M.n))) (hsize : 8192≤size)
    (hSl : ∀ x∈slots,Sl x) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv K.M base size m Sl V E s) (hV : ∀ x∈inputs,x∈V)
    (h2 : E 5400=E K.E.z*E K.E.z) (h3 : E 5432=E K.E.z*(E K.E.z*E K.E.z)) :
    WP isa ops.head s fun t =>
      ProgKeep K.M base (rcbW K.S K.D) s t ∧
      Inv K.M base size m Sl (validAfter head V) (runOps head E) t ∧
      runOps head E K.S.t3=E K.E.x*(E K.R.z*E K.R.z)-E K.R.x*(E K.E.z*E K.E.z) ∧
      runOps head E K.S.t5=E K.E.y*E K.R.z*(E K.R.z*E K.R.z)-E K.R.y*E K.E.z*(E K.E.z*E K.E.z) := by
  dsimp only [ops]
  refine WP.mono (Forward.Arithmetic.field_ok Forward.Arithmetic.cases (M:=K.M) hL hAl hm hsize head hI
    (fun op hop x hx => hSl x (slots_head op hop x hx)) (fun _ _ => Low.small (by decide) _) (readsOk_mono reads_head hV))
    fun t ⟨hk,hi⟩ => ⟨hk.mono ?_,hi,head_values E h2 h3⟩
  intro x hx
  obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
  exact writes_head op hop

theorem tail_ok {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hm : UnitMod m (2^(64*K.M.n))) (hsize : 8192≤size)
    (hSl : ∀ x∈slots,Sl x) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv K.M base size m Sl (validAfter head V) (runOps head E) s)
    (hV : ∀ x∈inputs,x∈V)
    (h2 : E 5400=E K.E.z*E K.E.z) (h3 : E 5432=E K.E.z*(E K.E.z*E K.E.z)) :
    WP isa ops.tail s fun t =>
      ProgKeep K.M base (rcbW K.S K.D) s t ∧
      Inv K.M base size m Sl ([K.D.x,K.D.y,K.D.z]++V) (runOps (head++tail) E) t ∧
      (runOps (head++tail) E K.D.x,runOps (head++tail) E K.D.y,runOps (head++tail) E K.D.z)=
        jacAddF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) (E K.E.z) := by
  have hr := readsOk_mono reads_full hV
  rw [readsOk_append,Bool.and_eq_true] at hr
  dsimp only [ops]
  refine WP.mono (Forward.Arithmetic.field_ok Forward.Arithmetic.cases (M:=K.M) hL hAl hm hsize tail hI
    (fun op hop x hx => hSl x (slots_tail op hop x hx)) (fun _ _ => Low.small (by decide) _) hr.2)
    fun t ⟨hk,hi⟩ => ⟨hk.mono ?_,?_,full_values E h2 h3⟩
  · intro x hx
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
    exact writes_tail op hop
  · rw [runOps_append]
    apply hi.sub
    intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (out_tail x hx)
    · exact Or.inl ((mem_validAfter _ _).mpr (Or.inl hx))

end VG.Proof.Weierstrass.AArch64.CachedField

end

/-! ## `CachedAdd` -/

section

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

/-- Complete Jacobian addition on public data, including all exceptional cases. -/
theorem add_ok {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hnc : Mont.callOf K.M = none)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hsize : 8192≤size) (hC : Law C) (ha : AM3 C)
    (hSlots : ∀ x∈slots,Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s) (hInputs : ∀ x∈inputs,x∈V)
    (h2 : E 5400=E K.E.z*E K.E.z) (h3 : E 5432=E K.E.z*(E K.E.z*E K.E.z))
    (hOne : K.one < C.p) {P Q : Point C} (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (hJP : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) P) (hJQ : InvJ C (E K.E.x) (E K.E.y) (E K.E.z) Q) :
    WP isa (CachedJac.add K ops) s
      (JacPost K.M K.S base size C Sl V K.D (Spec.Weierstrass.add P Q) s) := by
  have hA : RcbApart K.S K.R K.E K.D := by exact ⟨by decide +kernel,by decide +kernel⟩
  have hSl : ∀ x∈rcbW K.S K.D ++ rcbR K.S K.R K.E,Sl x := by
    intro x hx
    exact hSlots x (by simpa only [slots,inputs,List.append_assoc] using List.mem_append_left [5400,5432] hx)
  have hV : ∀ x∈rcbR K.S K.R K.E,x∈V := fun x hx => hInputs x (List.mem_append_left _ hx)
  rw [CachedJac.add]
  change WP isa _ s _
  apply fieldBranch_ok hL hAl hm hI (hV K.R.z (by simp [rcbR]))
  · intro a ia ka hz
    have hp := (hJP.z_zero_iff hC).mp hz
    rw [hp]
    exact WP.mono (copyPointJ_ok hL hAl hA hSl ia hV hJQ)
      (fun t ht => ht.prefix (ka.mono (by simp)))
  · intro a ia ka hpz
    apply fieldBranch_ok hL hAl hm ia (hV K.E.z (by simp [rcbR]))
    · intro b ib kb hz
      have hq := (hJQ.z_zero_iff hC).mp hz
      have hs : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.E K.R, Sl x := by
        intro x hx
        rw [List.mem_append,rcbR_swap_mem] at hx
        exact hSl x (List.mem_append.mpr hx)
      have hv : ∀ x ∈ rcbR K.S K.E K.R, x ∈ V := fun x hx => hV x ((rcbR_swap_mem _ _ _ _).mp hx)
      have hadd : Spec.Weierstrass.add P Q = P := by rw [hq]; cases P <;> rfl
      rw [hadd]
      exact WP.mono (copyPointJ_ok hL hAl hA.swap hs ib hv hJP)
        (fun t ht => (ht.prefix (kb.mono (by simp))).prefix (ka.mono (by simp)))
    · intro b ib kb hqz
      apply WP.seq
      refine WP.mono (head_ok hL hAl hm hsize hSlots ib hInputs h2 h3) fun c ⟨kc,ic,eh,er⟩ => ?_
      let EH := runOps head E
      have hkeep := (ka.mono (W' := rcbW K.S K.D) (by simp)).trans
        ((kb.mono (by simp)).trans kc)
      have hpkeep : ∀ x ∈ rcbR K.S K.R K.E, EH x = E x := fun x hx => head_readonly E (List.mem_append_left _ hx)
      have jp : InvJ C (EH K.R.x) (EH K.R.y) (EH K.R.z) P := by
        rw [hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR])]
        exact hJP
      have oldV : ∀ x ∈ V, x ∈ validAfter head V :=
        fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
      have hv : ∀ x ∈ rcbR K.S K.R K.R, x ∈ validAfter head V :=
        fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
      apply fieldBranch_ok hL hAl hm ic (a := K.S.t3) (by
        rw [mem_validAfter]; right; decide +kernel)
      · intro d id kd hz
        have hx : E K.E.x*(E K.R.z*E K.R.z)-E K.R.x*(E K.E.z*E K.E.z)=0 := eh.symm.trans hz
        apply fieldBranch_ok hL hAl hm id (a := K.S.t5) (by
          rw [mem_validAfter]; right; decide +kernel)
        · intro e ie ke hrz
          have hy : E K.E.y*E K.R.z*(E K.R.z*E K.R.z)-E K.R.y*E K.E.z*(E K.E.z*E K.E.z)=0 := er.symm.trans hrz
          have hpq := hJP.same hC hJQ hpz hqz hx hy
          have hdA : RcbApart K.S K.R K.R K.D := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
          have hdSl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.R, Sl x := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hSl x (List.mem_append_left _ hx)
            · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
          rw [←hpq]
          dsimp only [ops]
          refine WP.mono (Forward.double_ok Forward.Production.cases hL hAl hnc hm hC ha hdA hdSl ie hv hP jp) fun t ⟨kt,it,jt⟩ => ?_
          exact (JacPost.sub ⟨_,kt,it,jt⟩ oldV).prefix
            (hkeep.trans ((kd.mono (by simp)).trans (ke.mono (by simp))))
        · intro e ie ke hrz
          have hy : E K.E.y*E K.R.z*(E K.R.z*E K.R.z)-E K.R.y*E K.E.z*(E K.E.z*E K.E.z)≠0 := fun he => hrz (er.trans he)
          have hadd := hJP.opposite hC hP hQ hJQ hpz hqz hx hy
          rw [hadd]
          refine WP.mono (infinityPoint_ok hL hAl
            (fun x hx => hSl x (by
              simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
              rcases hx with rfl | rfl | rfl <;> simp [rcbW])) ie hOne) fun t ht => ?_
          exact (JacPost.sub ht oldV).prefix
            (hkeep.trans ((kd.mono (by simp)).trans (ke.mono (by simp))))
      · intro d id kd hz
        have hh : E K.E.x*(E K.R.z*E K.R.z)-E K.R.x*(E K.E.z*E K.E.z)≠0 := fun he => hz (eh.trans he)
        refine WP.mono (tail_ok hL hAl hm hsize hSlots id hInputs h2 h3) fun t ⟨kt,it,ht⟩ => ?_
        have jt := hJP.add_ne hC ha hP hQ hJQ hpz hqz hh
        dsimp only at jt
        rw [←ht] at jt
        exact JacPost.prefix ⟨_,kt,it,jt⟩ (hkeep.trans (kd.mono (by simp)))

end VG.Proof.Weierstrass.AArch64.CachedField

end

/-! ## `CachedAddTiming` -/

section

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
          (fun op hop x hx => hSlots x (slots_head op hop x hx)) (fun _ _ => Low.small (by decide) _) (readsOk_mono reads_head hInputs) (by simpa only [ops] using hc.head)
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
          have hd := Forward.field_outputs_relCT Forward.Production.cases (base:=base) (E:=runOps head E) hL hAl (callOf_small (by decide)) hm hdA hdSl hv (by simpa only [ops] using hc.double)
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
            (fun op hop x hx => hSlots x (slots_tail op hop x hx)) (fun _ _ => Low.small (by decide) _) hr.2 (by simpa only [ops] using hc.tail)
          rw [runOps_append]
          exact ht.mono (fun _ _ h => h) (fun _ _ h => h.sub (by
            intro x hx
            rw [mem_validAfter]
            rcases List.mem_append.mp hx with hx | hx
            · exact Or.inr (out_tail x hx)
            · exact Or.inl ((mem_validAfter _ _).mpr (Or.inl hx))))
        exact ht.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)

end VG.Proof.Weierstrass.AArch64.CachedField

end
