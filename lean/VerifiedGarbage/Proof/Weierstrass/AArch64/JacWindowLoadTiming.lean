import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming

/-! Relational equality through a public Jacobian table load. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

theorem jacLoadAtFields_ok {K : WinCfg} {base : Addr} {size a : Nat} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hn : K.M.n=4) (hy : K.E.y=K.E.x+32) (hz : K.E.z=K.E.x+64)
    {V : List Nat} {E : Nat → Spec.Weierstrass.Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (h16 : s.gpr .x16 = off base (K.tbl+96*(a-1)))
    (hD : ∀ x ∈ [K.E.x,K.E.y,K.E.z], Sl x)
    (hT : ∀ x ∈ [(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z], x ∈ V)
    (hap : K.E.x+96 ≤ K.tbl+96*(a-1) ∨ K.tbl+96*(a-1)+96 ≤ K.E.x)
 :
    WP isa (.block ((List.range 12).flatMap fun i => [.ldr .x .x4 .x16 (8*i),st .x4 (K.E.x+8*i)])) s fun t =>
      ProgKeep K.M base [K.E.x,K.E.y,K.E.z] s t ∧
      Inv K.M base size C.p Sl ([K.E.x,K.E.y,K.E.z]++V) (tmv C K.M.n base t) t ∧
      (tmv C K.M.n base t K.E.x,tmv C K.M.n base t K.E.y,tmv C K.M.n base t K.E.z) =
        (E (Jacobian.tablePt K a).x,E (Jacobian.tablePt K a).y,E (Jacobian.tablePt K a).z) := by
  have hdz := hL.le K.E.z (hD _ (by simp))
  have htz := hL.le (Jacobian.tablePt K a).z (hI.sl _ (hT _ (by simp)))
  have hnw := hI.scr.nowrap
  rw [hn,hz] at hdz
  simp only [Jacobian.tablePt,hn] at htz
  refine WP.mono (jacWords_ok (n := 12) hI.scr h16 (by omega)
    (hAl.sl _ (hD _ (by simp))) (by omega) hap 12 (Nat.le_refl _)) fun t ⟨hv,hk,ho⟩ => ?_
  have kp : ProgKeep K.M base [K.E.x,K.E.y,K.E.z] s t := by
    refine ⟨fun r hr => hk.gpr r (fun hh => hr ?_),hk.rd,hk.wr,hk.sp,fun x hx _ => ho x ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl <;> simp [clob]
    · have hx₀ := hx K.E.x (by simp)
      have hx₁ := hx K.E.y (by simp)
      have hx₂ := hx K.E.z (by simp)
      rw [hn] at hx₀ hx₁ hx₂
      rw [hy] at hx₁
      rw [hz] at hx₂
      omega
  have vx : wordsVal t.mem base K.E.x K.M.n = wordsVal s.mem base (Jacobian.tablePt K a).x K.M.n := by
    simpa only [hn,Jacobian.tablePt,Nat.mul_zero,Nat.add_zero] using jacWords_coord (c := 0) (by decide) hv
  have vy : wordsVal t.mem base K.E.y K.M.n = wordsVal s.mem base (Jacobian.tablePt K a).y K.M.n := by
    simpa only [hn,hy,Jacobian.tablePt,Nat.mul_one] using jacWords_coord (c := 1) (by decide) hv
  have vz : wordsVal t.mem base K.E.z K.M.n = wordsVal s.mem base (Jacobian.tablePt K a).z K.M.n := by
    simpa only [hn,hz,Jacobian.tablePt,show 32*2=64 from rfl] using jacWords_coord (c := 2) (by decide) hv
  have hlt : ∀ x ∈ [K.E.x,K.E.y,K.E.z], wordsVal t.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx]; exact hI.lt _ (hT _ (by simp))
    · rw [vy]; exact hI.lt _ (hT _ (by simp))
    · rw [vz]; exact hI.lt _ (hT _ (by simp))
  refine ⟨kp,hI.of_progKeep hL kp hD hlt,?_⟩
  unfold tmv
  rw [vx,vy,vz,hI.val _ (hT _ (by simp)),hI.val _ (hT _ (by simp)),hI.val _ (hT _ (by simp))]


theorem jacPublicFields_ok {K : WinCfg} {base : Addr} {size a : Nat} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hn : K.M.n=4) (hy : K.E.y=K.E.x+32) (hz : K.E.z=K.E.x+64)
    {V : List Nat} {E : Nat → Spec.Weierstrass.Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (h2 : s.gpr .x2 = BitVec.ofNat 64 a) (ha : 1 ≤ a) (ht : K.tbl < 4096)
    (hD : ∀ x ∈ [K.E.x,K.E.y,K.E.z], Sl x)
    (hT : ∀ x ∈ [(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z], x ∈ V)
    (hap : K.E.x+96 ≤ K.tbl+96*(a-1) ∨ K.tbl+96*(a-1)+96 ≤ K.E.x)
 :
    WP isa (.block (Jacobian.publicEntry K)) s fun t =>
      ProgKeep K.M base [K.E.x,K.E.y,K.E.z] s t ∧
      Inv K.M base size C.p Sl ([K.E.x,K.E.y,K.E.z]++V) (tmv C K.M.n base t) t ∧
      (tmv C K.M.n base t K.E.x,tmv C K.M.n base t K.E.y,tmv C K.M.n base t K.E.z) =
        (E (Jacobian.tablePt K a).x,E (Jacobian.tablePt K a).y,E (Jacobian.tablePt K a).z) := by
  rw [Jacobian.publicEntry,WP.block_append_iff]
  refine WP.mono (jacAddress_ok K hI.scr.x0 h2 ha ht) fun u ⟨h16,hk⟩ => ?_
  refine WP.mono (jacLoadAtFields_ok hL hAl hn hy hz (hI.of_keeps hk (by decide)) h16 hD hT hap)
    fun t ⟨kt,it,vt⟩ => ⟨?_,it,vt⟩
  have kp : ProgKeep K.M base [K.E.x,K.E.y,K.E.z] s u := by
    refine ⟨fun r hr => hk.gpr r (fun hh => hr ?_),hk.rd,hk.wr,hk.sp,fun _ _ _ => congrFun hk.mem _⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl | rfl | rfl <;> simp [clob]
  exact kp.trans kt

theorem jacLoadAt_relCT {K : WinCfg} {base : Addr} {size a : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hn : K.M.n=4) (hy : K.E.y=K.E.x+32) (hz : K.E.z=K.E.x+64)
    {V : List Nat} {E : Nat → Fe C}
    (hD : ∀ x∈jacCoords K.E, Sl x)
    (hT : ∀ x∈jacCoords (Jacobian.tablePt K a), x∈V)
    (hap : K.E.x+96≤K.tbl+96*(a-1) ∨ K.tbl+96*(a-1)+96≤K.E.x)
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x16]))
      (.block ((List.range 12).flatMap fun i => [.ldr .x .x4 .x16 (8*i),st .x4 (K.E.x+8*i)]))) :
    RelCT isa (fun s t => FieldPair K.M base size C.p Sl V E s t ∧
      s.gpr .x16=off base (K.tbl+96*(a-1)) ∧ t.gpr .x16=off base (K.tbl+96*(a-1)))
      (.block ((List.range 12).flatMap fun i => [.ldr .x .x4 .x16 (8*i),st .x4 (K.E.x+8*i)]))
      (fun s t => ∃ E', FieldPair K.M base size C.p Sl (jacCoords K.E++V) E' s t) := by
  let q := Jacobian.tablePt K a
  let F := fun x => if x=K.E.x then E q.x else if x=K.E.y then E q.y else E q.z
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
    refine WP.mono (jacLoadAtFields_ok hL hAl hn hy hz hi hp hD hT hap)
      fun t ⟨hk,it,ht⟩ => ⟨_,hk,it,?_⟩
    intro x _ hx
    simp only [Prod.mk.injEq] at ht
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · simpa only [F,ite_true] using ht.1
    · simpa only [F,show K.E.y ≠ K.E.x by omega,ite_false,ite_true] using ht.2.1
    · simpa only [F,show K.E.z ≠ K.E.x by omega,show K.E.z ≠ K.E.y by omega,ite_false] using ht.2.2

theorem jacPublic_relCT {K : WinCfg} {base : Addr} {size a : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hn : K.M.n=4) (hy : K.E.y=K.E.x+32) (hz : K.E.z=K.E.x+64)
    {V : List Nat} {E : Nat → Fe C}
    (hD : ∀ x∈jacCoords K.E, Sl x)
    (hT : ∀ x∈jacCoords (Jacobian.tablePt K a), x∈V)
    (hap : K.E.x+96≤K.tbl+96*(a-1) ∨ K.tbl+96*(a-1)+96≤K.E.x)
    (ha : 1 ≤ a) (ht : K.tbl < 4096)
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x2]))
      (.block (Jacobian.publicEntry K))) :
    RelCT isa (fun s t => FieldPair K.M base size C.p Sl V E s t ∧
      s.gpr .x2=BitVec.ofNat 64 a ∧ t.gpr .x2=BitVec.ofNat 64 a)
      (.block (Jacobian.publicEntry K))
      (fun s t => ∃ E', FieldPair K.M base size C.p Sl (jacCoords K.E++V) E' s t) := by
  let q := Jacobian.tablePt K a
  let F := fun x => if x=K.E.x then E q.x else if x=K.E.y then E q.y else E q.z
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
    refine WP.mono (jacPublicFields_ok hL hAl hn hy hz hi hp ha ht hD hT hap)
      fun t ⟨hk,it,ht⟩ => ⟨_,hk,it,?_⟩
    intro x _ hx
    simp only [Prod.mk.injEq] at ht
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · simpa only [F,ite_true] using ht.1
    · simpa only [F,show K.E.y ≠ K.E.x by omega,ite_false,ite_true] using ht.2.1
    · simpa only [F,show K.E.z ≠ K.E.x by omega,show K.E.z ≠ K.E.y by omega,ite_false] using ht.2.2

end VG.Proof.Weierstrass.AArch64
