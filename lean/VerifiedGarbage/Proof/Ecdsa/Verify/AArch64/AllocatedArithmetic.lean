import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFieldTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointDigits
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointLoop
import VerifiedGarbage.Proof.P256.VerifyAllocated.Double
import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
import VerifiedGarbage.Proof.Weierstrass.JacInplace

/-! ## `AllocatedPointFrame` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

/-- The full point-loop work includes lookup negation and cached entry fields. -/
def work : List (Nat × Nat) := [(128,32),(512,544),(5400,64),(7104,576)]

theorem work_bounds : ∀ w∈work,w.1+w.2≤8192 := by decide

theorem work_stable : ∀ r∈jointStableRanges cfg,∀ w∈work,
    r.1+r.2≤w.1 ∨ w.1+w.2≤r.1 := by decide +kernel

theorem work_cover : ∀ w∈(jointWork cfg).map (·,8*K.M.n)++[(K.M.tmp,8*K.M.n)],
    ∃ r∈work,r.1≤w.1 ∧ w.1+w.2≤r.1+r.2 := by decide +kernel

theorem liftArithmetic {base : Addr} {s t : State}
    (h : Frame base Proof.P256.VerifyAllocated.work s t) : Frame base work s t :=
  h.mono (fun _ hr => hr) (by decide)

theorem liftProg {base : Addr} {W : List Nat} {s t : State}
    (h : ProgKeep K.M base W s t) (hw : ∀ x∈W,x∈jointWork cfg) : Frame base work s t :=
  AllocatedFrame.of_prog (h.mono hw) clob4_allocatedRegs work_cover

/-- Point results expose only their initialized field slots and wide frame. -/
def PointPost (base : Addr) (V : List Nat) (o : Pt) (P : Point C) (s t : State) : Prop :=
  ∃ E,Frame base work s t ∧ Inv K.M base 8192 C.p Sl ([o.x,o.y,o.z]++V) E t ∧
    InvJ C (E o.x) (E o.y) (E o.z) P

theorem PointPost.prefix {base : Addr} {V : List Nat} {o : Pt} {P : Point C} {s a t : State}
    (h : PointPost base V o P a t) (hk : Frame base work s a) : PointPost base V o P s t := by
  obtain ⟨E,kt,hi,hp⟩ := h
  exact ⟨E,hk.trans kt,hi,hp⟩

theorem PointPost.sub {base : Addr} {V V' : List Nat} {o : Pt} {P : Point C} {s t : State}
    (h : PointPost base V o P s t) (hv : ∀ x∈V',x∈V) : PointPost base V' o P s t := by
  obtain ⟨E,hk,hi,hp⟩ := h
  exact ⟨E,hk,hi.sub (fun x hx => (List.mem_append.mp hx).elim
    (List.mem_append_left _) (fun hx => List.mem_append_right _ (hv x hx))),hp⟩

theorem PointPost.of_jac {base : Addr} {V : List Nat} {P : Point C} {s t : State}
    (h : JacPost K.M K.S base 8192 C Sl V K.D P s t) : PointPost base V K.D P s t := by
  obtain ⟨E,hk,hi,hp⟩ := h
  exact ⟨E,liftProg hk (by decide +kernel),hi,hp⟩

end VG.Proof.Ecdsa.Verify.AArch64.Allocated

end

/-! ## `AllocatedArithmetic` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.P256.VerifyArithmetic Spec.Weierstrass

abbrev apart : RcbApart K.S K.R K.E K.D := ⟨by decide,by decide⟩

theorem cachedHead_ok (raw : RawCorrect) {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base 8192 C.p Sl V E s) (hv : ∀ x∈CachedField.inputs,x∈V)
    (h2 : E 5400=E K.E.z*E K.E.z) (h3 : E 5432=E K.E.z*(E K.E.z*E K.E.z)) :
    WP isa (VG.Impl.P256.VerifyAllocated.program .cachedHead) s fun t =>
      Frame base work s t ∧ Inv K.M base 8192 C.p Sl (validAfter CachedField.head V)
        (runOps CachedField.head E) t ∧
      runOps CachedField.head E K.S.t3=E K.E.x*(E K.R.z*E K.R.z)-E K.R.x*(E K.E.z*E K.E.z) ∧
      runOps CachedField.head E K.S.t5=E K.E.y*E K.R.z*(E K.R.z*E K.R.z)-E K.R.y*E K.E.z*(E K.E.z*E K.E.z) := by
  refine WP.mono (field_all_ok raw Proof.P256.VerifyAllocated.CachedHead.caseProof (by decide) hi
    (by decide +kernel) (readsOk_mono CachedField.reads_head hv))
    fun _ ⟨hk,hi⟩ => ⟨liftArithmetic hk,hi,CachedField.head_values E h2 h3⟩

theorem cachedTail_ok (raw : RawCorrect) {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base 8192 C.p Sl (validAfter CachedField.head V) (runOps CachedField.head E) s)
    (hv : ∀ x∈CachedField.inputs,x∈V)
    (h2 : E 5400=E K.E.z*E K.E.z) (h3 : E 5432=E K.E.z*(E K.E.z*E K.E.z)) :
    WP isa (VG.Impl.P256.VerifyAllocated.program .jacTail) s fun t =>
      Frame base work s t ∧ Inv K.M base 8192 C.p Sl ([K.D.x,K.D.y,K.D.z]++V)
        (runOps (CachedField.head++CachedField.tail) E) t ∧
      (runOps (CachedField.head++CachedField.tail) E K.D.x,
       runOps (CachedField.head++CachedField.tail) E K.D.y,
       runOps (CachedField.head++CachedField.tail) E K.D.z)=
        jacAddF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) (E K.E.z) := by
  have hr := readsOk_mono CachedField.reads_full hv
  rw [readsOk_append,Bool.and_eq_true] at hr
  refine WP.mono (field_all_ok raw Proof.P256.VerifyAllocated.JacTail.caseProof (by decide) hi
    (by decide +kernel) hr.2) fun _ ⟨hk,it⟩ => ⟨liftArithmetic hk,?_,CachedField.full_values E h2 h3⟩
  rw [runOps_append]
  apply it.sub
  intro x hx
  rw [mem_validAfter]
  rcases List.mem_append.mp hx with hx | hx
  · exact Or.inr (CachedField.out_tail x hx)
  · exact Or.inl ((mem_validAfter _ _).mpr (Or.inl hx))

private theorem mixedHead_values (E : Nat → Fe C) :
    runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E) K.S.t3=
      E K.E.x*(E K.R.z*E K.R.z)-E K.R.x ∧
    runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E) K.S.t5=
      E K.E.y*E K.R.z*(E K.R.z*E K.R.z)-E K.R.y := by
  have he := runOps_rename (rcbσ K.S K.R K.E K.D) jacMixedHeadN (jacMixedInit K.S K.R E)
    (fun op hop => apart.inj ((show ∀ op∈jacMixedHeadN,op.out<9 by decide) op hop))
  change (fun y => runOps (ofN jacMixedHeadN K.S K.R K.E K.D) (jacMixedInit K.S K.R E)
    (rcbσ K.S K.R K.E K.D y))=_ at he
  rw [←jacMixedHead_eq K.S K.R K.E K.D] at he
  rw [jacMixedInit_rename apart] at he
  exact ⟨(congrFun he 3).trans (jacMixedHeadN_run (fun i => E (rcbσ K.S K.R K.E K.D i))).1,
    (congrFun he 5).trans (jacMixedHeadN_run (fun i => E (rcbσ K.S K.R K.E K.D i))).2⟩

theorem mixedHead_ok (raw : RawCorrect) {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base 8192 C.p Sl (K.S.t4::K.S.t2::V) (jacMixedInit K.S K.R E) s)
    (hv : ∀ x∈rcbR K.S K.R K.E,x∈V) :
    WP isa (VG.Impl.P256.VerifyAllocated.program .mixedHead) s fun t =>
      Frame base work s t ∧
      Inv K.M base 8192 C.p Sl (validAfter (jacMixedHead K.S K.R K.E) (K.S.t4::K.S.t2::V))
        (runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E)) t ∧
      runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E) K.S.t3=E K.E.x*(E K.R.z*E K.R.z)-E K.R.x ∧
      runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E) K.S.t5=E K.E.y*E K.R.z*(E K.R.z*E K.R.z)-E K.R.y := by
  have hr : readsOk (operations .mixedHead) (K.S.t4::K.S.t2::rcbR K.S K.R K.E)=true := by decide
  have hr' := readsOk_mono hr (V':=K.S.t4::K.S.t2::V) (fun x hx => by
    simp only [List.mem_cons] at hx ⊢
    exact hx.elim Or.inl (fun hx => hx.elim (fun hx => Or.inr (Or.inl hx)) (fun hx => Or.inr (Or.inr (hv x hx)))))
  exact WP.mono (field_all_ok raw Proof.P256.VerifyAllocated.MixedHead.caseProof (by decide) hi
    (by decide +kernel) hr') fun _ ⟨hk,it⟩ => ⟨liftArithmetic hk,it,mixedHead_values E⟩

private theorem mixedFull_values (E : Nat → Fe C) :
    (runOps (jacMixedHead K.S K.R K.E++jacMixedTail K.S K.R K.E K.D) (jacMixedInit K.S K.R E) K.D.x,
     runOps (jacMixedHead K.S K.R K.E++jacMixedTail K.S K.R K.E K.D) (jacMixedInit K.S K.R E) K.D.y,
     runOps (jacMixedHead K.S K.R K.E++jacMixedTail K.S K.R K.E K.D) (jacMixedInit K.S K.R E) K.D.z)=
      jacAddF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) 1 := by
  let N := jacMixedHeadN++jacMixedTailN
  have he : jacMixedHead K.S K.R K.E++jacMixedTail K.S K.R K.E K.D=ofN N K.S K.R K.E K.D := by
    rw [jacMixedHead_eq K.S K.R K.E K.D,jacMixedTail_eq]
    simp only [N,ofN,List.map_append]
  rw [he]
  have hren := runOps_rename (rcbσ K.S K.R K.E K.D) N (jacMixedInit K.S K.R E)
    (fun op hop => apart.inj ((show ∀ op∈N,op.out<9 by decide) op hop))
  rw [jacMixedInit_rename apart] at hren
  exact (congrArg₂ Prod.mk (congrFun hren 6)
    (congrArg₂ Prod.mk (congrFun hren 7) (congrFun hren 8))).trans
    (jacMixedN_run (fun i => E (rcbσ K.S K.R K.E K.D i)))

theorem mixedTail_ok (raw : RawCorrect) {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base 8192 C.p Sl (validAfter (jacMixedHead K.S K.R K.E) (K.S.t4::K.S.t2::V))
      (runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E)) s)
    (hv : ∀ x∈rcbR K.S K.R K.E,x∈V) :
    WP isa (VG.Impl.P256.VerifyAllocated.program .mixedTail) s fun t =>
      Frame base work s t ∧ Inv K.M base 8192 C.p Sl ([K.D.x,K.D.y,K.D.z]++V)
        (runOps (jacMixedHead K.S K.R K.E++jacMixedTail K.S K.R K.E K.D) (jacMixedInit K.S K.R E)) t ∧
      (runOps (jacMixedHead K.S K.R K.E++jacMixedTail K.S K.R K.E K.D) (jacMixedInit K.S K.R E) K.D.x,
       runOps (jacMixedHead K.S K.R K.E++jacMixedTail K.S K.R K.E K.D) (jacMixedInit K.S K.R E) K.D.y,
       runOps (jacMixedHead K.S K.R K.E++jacMixedTail K.S K.R K.E K.D) (jacMixedInit K.S K.R E) K.D.z)=
        jacAddF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) 1 := by
  have hr : readsOk (operations .mixedHead++operations .mixedTail)
      (K.S.t4::K.S.t2::rcbR K.S K.R K.E)=true := by decide
  have hr' := readsOk_mono hr (V':=K.S.t4::K.S.t2::V) (fun x hx => by
    simp only [List.mem_cons] at hx ⊢
    exact hx.elim Or.inl (fun hx => hx.elim (fun hx => Or.inr (Or.inl hx)) (fun hx => Or.inr (Or.inr (hv x hx)))))
  rw [readsOk_append,Bool.and_eq_true] at hr'
  refine WP.mono (field_all_ok raw Proof.P256.VerifyAllocated.MixedTail.caseProof (by decide) hi
    (by decide +kernel) hr'.2) fun _ ⟨hk,it⟩ => ⟨liftArithmetic hk,?_,mixedFull_values E⟩
  rw [runOps_append]
  apply it.sub
  intro x hx
  rw [mem_validAfter]
  rcases List.mem_append.mp hx with hx | hx
  · exact Or.inr ((show ∀ x∈[K.D.x,K.D.y,K.D.z],x∈(operations .mixedTail).map FOp.out by decide) x hx)
  · exact Or.inl ((mem_validAfter _ _).mpr (Or.inl (by simp [hx])))

theorem double_ok (raw : RawCorrect) (hC : Law C) (ha : AM3 C)
    {base : Addr} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base 8192 C.p Sl (jointLive cfg) E s) {P : Point C}
    (hP : onCurve C P=true) (hj : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) P) :
    WP isa (VG.Impl.P256.VerifyAllocated.program .doubleRR) s fun t =>
      Frame base work s t ∧ Inv K.M base 8192 C.p Sl (jointLive cfg)
        (runOps (operations .doubleRR) E) t ∧
      InvJ C (runOps (operations .doubleRR) E K.R.x) (runOps (operations .doubleRR) E K.R.y)
        (runOps (operations .doubleRR) E K.R.z) (add P P) := by
  refine WP.mono (field_ok raw Proof.P256.VerifyAllocated.Double.caseProof hi (by decide +kernel)
    (by decide +kernel) (fun _ hx => (mem_validAfter _ _).mpr (Or.inl hx)) (by decide +kernel))
    fun _ ⟨hk,it⟩ => ⟨liftArithmetic hk,it,?_⟩
  exact InvJ.dbl' hC ha hP hj (dblJMul_inplace_run (by decide +kernel) E)

end VG.Proof.Ecdsa.Verify.AArch64.Allocated

end
