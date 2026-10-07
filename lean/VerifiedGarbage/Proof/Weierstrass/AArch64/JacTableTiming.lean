import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStore

/-! Exact field equality through public in-scratch table transfers. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem FieldPair.rebuild {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V V' W : List Nat} {E Es Et : Nat → Fin m} {s t s' t' : State}
    (hL : Lay M size Sl) (hp : FieldPair M base size m Sl V E s t)
    (ks : ProgKeep M base W s s') (kt : ProgKeep M base W t t')
    (hW : ∀ x∈W, Sl x) (hi : Inv M base size m Sl V' Es s') (hj : Inv M base size m Sl V' Et t')
    (hv : ∀ x∈V', x∈W ∨ x∈V) (hn : ∀ x∈V', x∈W → Es x=Et x) :
    FieldPair M base size m Sl V' Es s' t' := by
  refine ⟨hi,hj.congr_env ?_,ks.sp.trans (hp.sp.trans kt.sp.symm)⟩
  intro x hx
  by_cases hw : x∈W
  · exact (hn x hx hw).symm
  · have hold := (hv x hx).resolve_left hw
    rw [←hj.val x hx,←hi.val x hx,kt.slot hL hp.right.scr hW (hj.sl x hx) hw,
      ks.slot hL hp.left.scr hW (hi.sl x hx) hw,hp.right.val x hold,hp.left.val x hold]

theorem jacStoreFields_ok {K : WinCfg} {base : Addr} {size a : Nat} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl)
    (hn : K.M.n=4) (hy : K.R.y=K.R.x+32) (hz : K.R.z=K.R.x+64)
    {V : List Nat} {E : Nat → Spec.Weierstrass.Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (h20 : s.gpr .x20 = off base (K.tbl+96*(a-1))) (hr8 : K.R.x%8=0)
    (hD : ∀ x ∈ [(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z], Sl x)
    (hR : ∀ x ∈ [K.R.x,K.R.y,K.R.z], x ∈ V)
    (hap : K.R.x+96 ≤ K.tbl+96*(a-1) ∨ K.tbl+96*(a-1)+96 ≤ K.R.x)
 :
    WP isa (.block (Jacobian.tableStore K)) s fun t =>
      ProgKeep K.M base [(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z] s t ∧
      Inv K.M base size C.p Sl ([(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z]++V)
        (tmv C K.M.n base t) t ∧
      (tmv C K.M.n base t (Jacobian.tablePt K a).x,
       tmv C K.M.n base t (Jacobian.tablePt K a).y,
       tmv C K.M.n base t (Jacobian.tablePt K a).z) = (E K.R.x,E K.R.y,E K.R.z) := by
  have hrz := hL.le K.R.z (hI.sl _ (hR _ (by simp)))
  have hdz := hL.le (Jacobian.tablePt K a).z (hD _ (by simp))
  rw [hn,hz] at hrz
  simp only [Jacobian.tablePt,hn] at hdz
  refine WP.mono (jacStoreWords_ok (n := 12) hI.scr h20 (by omega) (by omega) hr8
    (Or.symm hap) 12 (Nat.le_refl _)) fun t ⟨hv,hk,ho⟩ => ?_
  have kp : ProgKeep K.M base [(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z] s t := by
    refine ⟨fun r hr => hk.gpr r (fun hh => hr ?_),hk.rd,hk.wr,hk.sp,fun x hx _ => ho x ?_⟩
    · simp only [List.mem_singleton] at hh
      subst hh; simp [clob]
    · have hx₀ := hx (Jacobian.tablePt K a).x (by simp)
      have hx₁ := hx (Jacobian.tablePt K a).y (by simp)
      have hx₂ := hx (Jacobian.tablePt K a).z (by simp)
      simp only [Jacobian.tablePt,hn] at hx₀ hx₁ hx₂
      omega
  have vx : wordsVal t.mem base (Jacobian.tablePt K a).x K.M.n = wordsVal s.mem base K.R.x K.M.n := by
    simpa only [hn,Jacobian.tablePt,Nat.mul_zero,Nat.add_zero] using jacWords_coord (c := 0) (by decide) hv
  have vy : wordsVal t.mem base (Jacobian.tablePt K a).y K.M.n = wordsVal s.mem base K.R.y K.M.n := by
    simpa only [hn,hy,Jacobian.tablePt,Nat.mul_one] using jacWords_coord (c := 1) (by decide) hv
  have vz : wordsVal t.mem base (Jacobian.tablePt K a).z K.M.n = wordsVal s.mem base K.R.z K.M.n := by
    simpa only [hn,hz,Jacobian.tablePt,show 32*2=64 from rfl] using jacWords_coord (c := 2) (by decide) hv
  have hlt : ∀ x ∈ [(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z],
      wordsVal t.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx]; exact hI.lt _ (hR _ (by simp))
    · rw [vy]; exact hI.lt _ (hR _ (by simp))
    · rw [vz]; exact hI.lt _ (hR _ (by simp))
  refine ⟨kp,hI.of_progKeep hL kp hD hlt,?_⟩
  unfold tmv
  rw [vx,vy,vz,hI.val _ (hR _ (by simp)),hI.val _ (hR _ (by simp)),hI.val _ (hR _ (by simp))]

/-- A public transfer writes the same values in the same slots in both runs. -/
theorem fieldWrite_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) {V V' W : List Nat} {E F : Nat → Fin m}
    {c : Prog isa} {Pre : State → Prop} {rs : List Reg}
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs rs)) c)
    (hpub : ∀ s t, FieldPair M base size m Sl V E s t → Pre s → Pre t →
      AArch64.Taint.Agree (Taint.ofRegs rs) s t)
    (hW : ∀ x∈W, Sl x) (hV : ∀ x∈V', x∈W ∨ x∈V)
    (hw : ∀ s, Inv M base size m Sl V E s → Pre s → WP isa c s fun t =>
      ∃ E', ProgKeep M base W s t ∧ Inv M base size m Sl V' E' t ∧
        ∀ x∈V', x∈W → E' x=F x) :
    RelCT isa (fun s t => FieldPair M base size m Sl V E s t ∧ Pre s ∧ Pre t) c
      (fun s t => ∃ E', FieldPair M base size m Sl V' E' s t) := by
  intro s t ts tt s' t' ⟨hp,ps,pt⟩ es et
  obtain ⟨_,_,xs,Es,ks,is,vs⟩ := hw s hp.left ps
  obtain ⟨_,_,xt,Et,kt,it,vt⟩ := hw t hp.right pt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  refine ⟨hct _ _ _ _ _ _ trivial trivial (hpub s t hp ps pt) es et,Es,?_⟩
  exact hp.rebuild hL ks kt hW is it hV (fun x hx hw => (vs x hx hw).trans (vt x hx hw).symm)

/-- The store address is public and the table inherits the accumulator's exact coordinates. -/
theorem jacStore_relCT {K : WinCfg} {base : Addr} {size a : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hn : K.M.n=4)
    (hy : K.R.y=K.R.x+32) (hz : K.R.z=K.R.x+64) (hr8 : K.R.x%8=0)
    {V : List Nat} {E : Nat → Fe C}
    (hD : ∀ x∈jacCoords (Jacobian.tablePt K a), Sl x)
    (hR : ∀ x∈jacCoords K.R, x∈V)
    (hap : K.R.x+96≤K.tbl+96*(a-1) ∨ K.tbl+96*(a-1)+96≤K.R.x)
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x20]))
      (.block (Jacobian.tableStore K))) :
    RelCT isa (fun s t => FieldPair K.M base size C.p Sl V E s t ∧
      s.gpr .x20=off base (K.tbl+96*(a-1)) ∧ t.gpr .x20=off base (K.tbl+96*(a-1)))
      (.block (Jacobian.tableStore K))
      (fun s t => ∃ E', FieldPair K.M base size C.p Sl (jacCoords (Jacobian.tablePt K a)++V) E' s t) := by
  let q := Jacobian.tablePt K a
  let F := fun x => if x=q.x then E K.R.x else if x=q.y then E K.R.y else E K.R.z
  apply fieldWrite_relCT (F:=F) hL hct
  · intro s t hp ps pt
    refine ⟨hp.sp,fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
    · exact ps.trans pt.symm
  · exact hD
  · intro x hx; exact List.mem_append.mp hx
  · intro s hi hp
    refine WP.mono (jacStoreFields_ok hL hn hy hz hi hp hr8 hD hR hap)
      fun t ⟨hk,it,ht⟩ => ⟨_,hk,it,?_⟩
    intro x _ hx
    simp only [Prod.mk.injEq] at ht
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · simpa only [F,q,ite_true] using ht.1
    · simpa only [F,q,Jacobian.tablePt,show K.tbl+96*(a-1)+32 ≠ K.tbl+96*(a-1) by omega,ite_false,ite_true] using ht.2.1
    · simpa only [F,q,Jacobian.tablePt,show K.tbl+96*(a-1)+64 ≠ K.tbl+96*(a-1) by omega,
        show K.tbl+96*(a-1)+64 ≠ K.tbl+96*(a-1)+32 by omega,ite_false] using ht.2.2

/-- Retain a known control register alongside a field relation. -/
theorem relCT_keepGpr {P Q : State → State → Prop} {c : Prog isa} {r : Reg} {v : BitVec 64}
    (h : RelCT isa P c Q) (hc : ∀ i∈instrs c, dstOf i≠some r) (hr : r∉linkRegs) :
    RelCT isa (fun s t => P s t ∧ s.gpr r=v ∧ t.gpr r=v) c
      (fun s t => Q s t ∧ s.gpr r=v ∧ t.gpr r=v) := by
  intro s t ts tt s' t' ⟨hp,ps,pt⟩ es et
  obtain ⟨he,hq⟩ := h _ _ _ _ _ _ hp es et
  exact ⟨he,hq,(Exec.gpr hc es (Or.inr hr)).trans ps,(Exec.gpr hc et (Or.inr hr)).trans pt⟩

/-- Public control-register updates do not alter initialized field values. -/
theorem keepsField_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {c : Prog isa}
    {Pre Post : State → Prop} {pub rs : List Reg} (h0 : Reg.x0∉rs)
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs pub)) c)
    (hpub : ∀ s t, FieldPair M base size m Sl V E s t → Pre s → Pre t →
      AArch64.Taint.Agree (Taint.ofRegs pub) s t)
    (hw : ∀ s, Inv M base size m Sl V E s → Pre s →
      WP isa c s fun t => Post t ∧ Keeps rs s t) :
    RelCT isa (fun s t => FieldPair M base size m Sl V E s t ∧ Pre s ∧ Pre t) c
      (fun s t => FieldPair M base size m Sl V E s t ∧ Post s ∧ Post t) := by
  intro s t ts tt s' t' ⟨hp,ps,pt⟩ es et
  obtain ⟨_,_,xs,qs,ks⟩ := hw s hp.left ps
  obtain ⟨_,_,xt,qt,kt⟩ := hw t hp.right pt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨hct _ _ _ _ _ _ trivial trivial (hpub s t hp ps pt) es et,
    ⟨hp.left.of_keeps ks h0,hp.right.of_keeps kt h0,ks.sp.trans (hp.sp.trans kt.sp.symm)⟩,qs,qt⟩

end VG.Proof.Weierstrass.AArch64
