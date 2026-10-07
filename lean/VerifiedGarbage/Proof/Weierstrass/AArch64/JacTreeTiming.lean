import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Production
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Timing
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTree
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoadTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! The public tree carries exact paired field values and fixed loop counters. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

abbrev RegCT (rs : List Reg) (c : Prog isa) :=
  ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs rs)) c

structure JacTreeChecks (K : WinCfg) : Prop where
  copyInit : FieldCT (.block (copyPt K.M.n K.R K.P))
  pointer : FieldCT (.block [.addImm .x .x20 .x0 K.tbl])
  store : RegCT [.x0,.x20] (.block (Jacobian.tableStore K))
  initCounter : RegCT [.x0,.x20] (.block [.addImm .x .x20 .x20 96,.movz .x .x19 15 0])
  parity : RegCT [.x19] (.block [.movz .x .x5 1 0,.logic .and .x .x2 .x19 .x5])
  fetchAddress : RegCT [.x0,.x19] (.block [.movz .x .x17 15 0,.sub .x .x17 .x17 .x19,
    .lsr .x .x17 .x17 1,.movz .x .x2 96 0,.mul .x .x17 .x17 .x2,
    .addImm .x .x16 .x0 K.tbl,.add .x .x16 .x16 .x17])
  fetchWords : RegCT [.x0,.x16] (.block ((List.range 12).flatMap fun i =>
    [.ldr .x .x4 .x16 (8*i),st .x4 (K.E.x+8*i)]))
  double : FieldCT (VG.Impl.P256.VerifyDouble.double K.M K.S K.E K.D)
  add : JacAddChecks K K.R K.P K.D
  copyStep : FieldCT (.block (copyPt K.M.n K.R K.D))
  advance : RegCT [.x19,.x20] (.block [.addImm .x .x20 .x20 96,decCounter])
  keepArithmetic : ∀ r∈[Reg.x19,Reg.x20], ∀ i∈instrs (Jacobian.jacTreeArithmetic K 16), dstOf i≠some r

 theorem tableStore_preserves (K : WinCfg) {r : Reg} (hr : r≠.x4) :
    ∀ i∈instrs (.block (Jacobian.tableStore K) : Prog isa), dstOf i≠some r := by
  intro i hi
  change i∈(List.range 12).flatMap (fun j => [ld .x4 (K.R.x+8*j),.str .x .x4 .x20 (8*j)]) at hi
  obtain ⟨j,_,hi⟩ := List.mem_flatMap.mp hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl
  · change some Reg.x4 ≠ some r
    intro he; exact hr (Option.some.inj he).symm
  · change none ≠ some r
    intro he; cases he

 theorem jacTree_init_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : JacWinLay K size) (hAl : Aligned K.M (·∈jacWinSlots K))
    (ht : K.tbl<4096) (hc : JacTreeChecks K) {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (·∈jacWinSlots K) (winRo K) E)
      (.block (copyPt 4 K.R K.P ++ [.addImm .x .x20 .x0 K.tbl] ++ Jacobian.tableStore K ++
        [.addImm .x .x20 .x20 96,.movz .x .x19 15 0]))
      (fun s t => ∃ E', FieldPair K.M base size C.p (·∈jacWinSlots K) (jacTreeLive K 1) E' s t ∧
        s.gpr .x19=15 ∧ t.gpr .x19=15 ∧
        s.gpr .x20=off base (K.tbl+96) ∧ t.gpr .x20=off base (K.tbl+96)) := by
  have rs : ∀ x∈[K.R.x,K.R.y,K.R.z], x∈jacWinSlots K := by
    intro x hx; apply List.mem_append_left
    simp only [winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have rp : ∀ x∈[K.P.x,K.P.y,K.P.z], x∈winRo K := by
    intro x hx; simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have sep : K.R.x+96≤K.tbl ∨ K.tbl+96≤K.R.x := by
    have hx := hL.tbl K.R.x (by simp [winOther])
    have hz := hL.tbl K.R.z (by simp [winOther])
    rw [hL.rxz] at hz
    omega
  rw [List.append_assoc,List.append_assoc,← hL.n]
  apply RelCT.block_append
  apply RelCT.seq (copyPoint_relCT hL.lay hAl rs rp hc.copyInit)
  apply RelCT.block_append
  have ptr := keepsField_relCT (M:=K.M) (base:=base) (size:=size) (m:=C.p)
    (Sl:=(·∈jacWinSlots K)) (V:=[K.R.x,K.R.y,K.R.z]++winRo K) (E:=copyPointEnv E K.R K.P)
    (Pre:=fun _ => True) (Post:=fun s => s.gpr .x20=off base K.tbl)
    (by decide : Reg.x0∉[Reg.x20]) hc.pointer
    (fun _ _ hp _ _ => hp.public) (fun s hi _ => jacTree_pointer_ok hi.scr ht)
  apply RelCT.seq (ptr.mono (fun _ _ hp => ⟨hp,trivial,trivial⟩) (fun _ _ hp => hp))
  apply RelCT.block_append
  have store := jacStore_relCT (base:=base) (V:=[K.R.x,K.R.y,K.R.z]++winRo K) (a:=1) hL.lay hL.n hL.rxy hL.rxz (hAl.sl _ (rs _ (by simp)))
    (E:=copyPointEnv E K.R K.P) (jacTblPt_mem K (by decide) (by decide))
    (fun _ hx => List.mem_append_left _ hx) (by simpa using sep) hc.store
  have storeKeep := relCT_keepGpr (r:=.x20) (v:=off base K.tbl) store
    (tableStore_preserves K (by decide)) (by decide)
  apply RelCT.seq (storeKeep.mono
    (Q':=fun (s t : State) => ∃ e, FieldPair K.M base size C.p (·∈jacWinSlots K)
      (jacCoords (Jacobian.tablePt K 1)++([K.R.x,K.R.y,K.R.z]++winRo K)) e s t ∧
      s.gpr .x20=off base K.tbl ∧ t.gpr .x20=off base K.tbl)
    (fun _ _ hp => ⟨hp,hp.2⟩) (fun _ _ ⟨⟨e,hp⟩,hs,ht⟩ => ⟨e,hp,hs,ht⟩))
  apply RelCT.exists_
  intro E'
  have ctr := keepsField_relCT (M:=K.M) (base:=base) (size:=size) (m:=C.p)
    (Sl:=(·∈jacWinSlots K)) (V:=jacCoords (Jacobian.tablePt K 1)++([K.R.x,K.R.y,K.R.z]++winRo K)) (E:=E')
    (Pre:=fun s => s.gpr .x20=off base K.tbl)
    (Post:=fun s => s.gpr .x20=off base (K.tbl+96) ∧ s.gpr .x19=15)
    (by decide : Reg.x0∉[Reg.x19,Reg.x20]) hc.initCounter
    (fun s t hp ps pt => ⟨hp.sp,fun r hr => by
      simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
      · exact ps.trans pt.symm⟩)
    (fun s _ hp => WP.mono (jacTree_initCounter_ok hp) (fun _ ⟨hp,hc,hk⟩ => ⟨⟨hp,hc⟩,hk⟩))
  exact ctr.mono (fun _ _ hp => hp) (fun s t ⟨hp,hs,ht⟩ => ⟨E',hp.sub (by
    intro x hx
    simp only [jacTreeLive,jacTreeSlots,jacCoords,Jacobian.tablePt,show ¬2≤1 by decide,↓reduceIte,
      List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,List.nil_append,
      List.append_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind),hs.2,ht.2,hs.1,ht.1⟩)

 theorem jacTreeFetch_relCT {K : WinCfg} {C : Curve} {base : Addr} {size a : Nat}
    (hL : JacWinLay K size) (hAl : Aligned K.M (·∈jacWinSlots K)) (ht : K.tbl<4096)
    (ha : 1≤a) (ha8 : a≤8) (hc : JacTreeChecks K) {V : List Nat} {E : Nat → Fe C}
    (hT : ∀ x∈jacCoords (Jacobian.tablePt K a), x∈V) :
    RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) V E s t ∧
      s.gpr .x19=BitVec.ofNat 64 (15-2*(a-1)) ∧ t.gpr .x19=BitVec.ofNat 64 (15-2*(a-1)))
      (.block (Jacobian.jacTreeFetch K 16))
      (fun s t => ∃ E', FieldPair K.M base size C.p (·∈jacWinSlots K) (jacCoords K.E++V) E' s t) := by
  have es : ∀ x∈jacCoords K.E, x∈jacWinSlots K := by
    intro x hx; apply List.mem_append_left
    simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have sep : K.E.x+96≤K.tbl+96*(a-1) ∨ K.tbl+96*(a-1)+96≤K.E.x := by
    have hx := hL.tbl K.E.x (by simp [winOther])
    have hz := hL.tbl K.E.z (by simp [winOther])
    rw [hL.exz] at hz
    omega
  rw [Jacobian.jacTreeFetch]
  apply RelCT.block_append
  have head := keepsField_relCT (M:=K.M) (base:=base) (size:=size) (m:=C.p)
    (Sl:=(·∈jacWinSlots K)) (V:=V) (E:=E)
    (Pre:=fun s => s.gpr .x19=BitVec.ofNat 64 (15-2*(a-1)))
    (Post:=fun s => s.gpr .x16=off base (K.tbl+96*(a-1)))
    (by decide : Reg.x0∉[Reg.x2,Reg.x16,Reg.x17]) hc.fetchAddress
    (fun s t hp ps pt => ⟨hp.sp,fun r hr => by
      simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
      · exact ps.trans pt.symm⟩)
    (fun s hi hp => jacTreeAddress_ok K hi.scr.x0 hp ha ha8 ht)
  exact RelCT.seq head (jacLoadAt_relCT hL.lay hAl hL.n hL.exy hL.exz es hT sep hc.fetchWords)

 theorem jacTreeArithmetic_relCT {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (ht : K.tbl<4096) (hOne : K.one<C.p)
    (hm1 : 1≤m) (hm15 : m≤15) (hc : JacTreeChecks K) {E : Nat → Fe C} :
    RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (jacTreeLive K m) E s t ∧
      s.gpr .x19=BitVec.ofNat 64 (16-m) ∧ t.gpr .x19=BitVec.ofNat 64 (16-m))
      (Jacobian.jacTreeArithmetic K 16)
      (fun s t => ∃ E', FieldPair K.M base size C.p (·∈jacWinSlots K)
        ([K.E.x,K.E.y,K.E.z,K.D.x,K.D.y,K.D.z]++jacTreeLive K m) E' s t) := by
  have old := hL.toWinLay hJ
  have aslots : ∀ x∈rcbW K.S K.D ++ rcbR K.S K.R K.P, x∈jacWinSlots K := by
    intro x hx; apply List.mem_append_left
    simp only [rcbW,rcbR,winRo,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have dslots : ∀ x∈rcbW K.S K.D ++ rcbR K.S K.E K.E, x∈jacWinSlots K := by
    intro x hx; apply List.mem_append_left
    simp only [rcbW,rcbR,winRo,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have pv := jacTreeLive_read K m
  have vtab := jacTreeLive_table K (a:=(m+1)/2) (m:=m) (by omega) (by omega)
  intro s t ts tt s' t' ⟨hp,ps,pt⟩ es et
  cases es with
  | seq qs bs =>
    cases et with
    | seq qt bt =>
      obtain ⟨_,_,xs,cs,ks⟩ := jacTreeParity_ok (by omega) ps
      obtain ⟨_,_,xt,ct,kt⟩ := jacTreeParity_ok (by omega) pt
      obtain ⟨_,rfl⟩ := Exec.det qs xs
      obtain ⟨_,rfl⟩ := Exec.det qt xt
      have pair : FieldPair K.M base size C.p (·∈jacWinSlots K) (jacTreeLive K m) E _ _ :=
        ⟨hp.left.of_keeps ks (by decide),hp.right.of_keeps kt (by decide),ks.sp.trans (hp.sp.trans kt.sp.symm)⟩
      have pq : AArch64.Taint.Agree (Taint.ofRegs [.x19]) s t := by
        refine ⟨hp.sp,fun r hr => ?_⟩
        simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
        subst r; exact ps.trans pt.symm
      have tq := hc.parity _ _ _ _ _ _ trivial trivial pq qs qt
      have cond := cs.trans ct.symm
      have even : m%2=1 → RelCT isa
          (fun u v => FieldPair K.M base size C.p (·∈jacWinSlots K) (jacTreeLive K m) E u v ∧
            u.gpr .x19=BitVec.ofNat 64 (16-m) ∧ v.gpr .x19=BitVec.ofNat 64 (16-m))
          (.seq (.block (Jacobian.jacTreeFetch K 16)) (VG.Impl.P256.VerifyDouble.double K.M K.S K.E K.D))
          (fun u v => ∃ E', FieldPair K.M base size C.p (·∈jacWinSlots K)
            ([K.E.x,K.E.y,K.E.z,K.D.x,K.D.y,K.D.z]++jacTreeLive K m) E' u v) := by
        intro ho
        have cc : 16-m=15-2*((m+1)/2-1) := by omega
        have fetch := jacTreeFetch_relCT (base:=base) hL hAl ht (by omega) (by omega) hc (E:=E) vtab
        apply RelCT.seq (fetch.mono (fun _ _ h => by simpa only [cc] using h) (fun _ _ h => h))
        apply RelCT.exists_
        intro e
        have dv : ∀ x∈rcbR K.S K.E K.E, x∈jacCoords K.E++jacTreeLive K m := by
          intro x hx
          have a := pv K.S.a (by simp [rcbR]); have b := pv K.S.b3 (by simp [rcbR])
          simp only [rcbR,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
        have d := Forward.field_outputs_relCT Forward.Production.cases (base:=base) (E:=e) hL.lay hAl hm
          old.rcbApart_jac.2.1 dslots dv hc.double
        exact d.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub (by
          intro x hx
          simp only [jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)⟩)
      have odd : m%2≠1 → RelCT isa (FieldPair K.M base size C.p (·∈jacWinSlots K) (jacTreeLive K m) E)
          (Jacobian.jacAdd K K.R K.P K.D)
          (fun u v => ∃ E', FieldPair K.M base size C.p (·∈jacWinSlots K)
            ([K.E.x,K.E.y,K.E.z,K.D.x,K.D.y,K.D.z]++jacTreeLive K m) E' u v) := by
        intro ho
        apply (jacAdd_relCT hL.lay hAl hm (hL.rcbApart_RP hJ) aslots pv hOne hc.add).mono (fun _ _ h => h)
        intro u v ⟨e,hp⟩
        refine ⟨e,hp.sub ?_⟩
        intro x hx
        have ex := jacTreeLive_ED K (m:=m) (by omega) K.E.x (by simp)
        have ey := jacTreeLive_ED K (m:=m) (by omega) K.E.y (by simp)
        have ez := jacTreeLive_ED K (m:=m) (by omega) K.E.z (by simp)
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
      cases bs with
      | iteT hs bs =>
        cases bt with
        | iteF ht _ => rw [cond,ht] at hs; cases hs
        | iteT _ bt =>
          have ho := of_decide_eq_true (Option.some.inj (cs.symm.trans hs))
          obtain ⟨eq,hout⟩ := even ho _ _ _ _ _ _
            ⟨pair,(ks.gpr _ (by decide)).trans ps,(kt.gpr _ (by decide)).trans pt⟩ bs bt
          exact ⟨by rw [tq,eq],hout⟩
      | iteF hs bs =>
        cases bt with
        | iteT ht _ => rw [cond,ht] at hs; cases hs
        | iteF _ bt =>
          have ho := of_decide_eq_false (Option.some.inj (cs.symm.trans hs))
          obtain ⟨eq,hout⟩ := odd ho _ _ _ _ _ _ pair bs bt
          exact ⟨by rw [tq,eq],hout⟩

 def TreePair (K : WinCfg) (C : Curve) (base : Addr) (size m : Nat) (s t : State) : Prop :=
  ∃ E, FieldPair K.M base size C.p (·∈jacWinSlots K) (jacTreeLive K m) E s t ∧
    s.gpr .x19=BitVec.ofNat 64 (16-m) ∧ t.gpr .x19=BitVec.ofNat 64 (16-m) ∧
    s.gpr .x20=off base (K.tbl+96*m) ∧ t.gpr .x20=off base (K.tbl+96*m)

 theorem relCT_keepControls {P Q : State → State → Prop} {c : Prog isa} {a b : BitVec 64}
    (h : RelCT isa P c Q) (hc : ∀ r∈[Reg.x19,Reg.x20], ∀ i∈instrs c, dstOf i≠some r) :
    RelCT isa (fun s t => P s t ∧ s.gpr .x19=a ∧ t.gpr .x19=a ∧ s.gpr .x20=b ∧ t.gpr .x20=b) c
      (fun s t => Q s t ∧ s.gpr .x19=a ∧ t.gpr .x19=a ∧ s.gpr .x20=b ∧ t.gpr .x20=b) := by
  intro s t ts tt s' t' ⟨hp,s19,t19,s20,t20⟩ es et
  obtain ⟨he,hq⟩ := h _ _ _ _ _ _ hp es et
  exact ⟨he,hq,(Exec.gpr (hc _ (by simp)) es).trans s19,(Exec.gpr (hc _ (by simp)) et).trans t19,
    (Exec.gpr (hc _ (by simp)) es).trans s20,(Exec.gpr (hc _ (by simp)) et).trans t20⟩

 theorem jacTree_step_relCT {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (ht : K.tbl<4096) (hOne : K.one<C.p)
    (hm1 : 1≤m) (hm15 : m≤15) (hc : JacTreeChecks K)
    (hcopy : ∀ r∈[Reg.x19,Reg.x20], ∀ i∈instrs (.block (copyPt K.M.n K.R K.D) : Prog isa), dstOf i≠some r) :
    RelCT isa (TreePair K C base size m) (Jacobian.jacTreeStep K 16) (TreePair K C base size (m+1)) := by
  have rs : ∀ x∈jacCoords K.R, x∈jacWinSlots K := by
    intro x hx; apply List.mem_append_left
    simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have sep : K.R.x+96≤K.tbl+96*m ∨ K.tbl+96*m+96≤K.R.x := by
    have hx := hL.tbl K.R.x (by simp [winOther])
    have hz := hL.tbl K.R.z (by simp [winOther])
    rw [hL.rxz] at hz
    omega
  unfold TreePair
  apply RelCT.exists_
  intro E
  unfold Jacobian.jacTreeStep
  have ac := jacTreeArithmetic_relCT (base:=base) hL hJ hAl hm ht hOne hm1 hm15 hc (E:=E)
  have ak := relCT_keepControls (a:=BitVec.ofNat 64 (16-m)) (b:=off base (K.tbl+96*m)) ac hc.keepArithmetic
  apply RelCT.seq (ak.mono
    (Q':=fun (s t : State) => ∃ e, FieldPair K.M base size C.p (·∈jacWinSlots K)
      ([K.E.x,K.E.y,K.E.z,K.D.x,K.D.y,K.D.z]++jacTreeLive K m) e s t ∧
      s.gpr .x19=BitVec.ofNat 64 (16-m) ∧ t.gpr .x19=BitVec.ofNat 64 (16-m) ∧
      s.gpr .x20=off base (K.tbl+96*m) ∧ t.gpr .x20=off base (K.tbl+96*m))
    (fun _ _ ⟨hp,s19,t19,s20,t20⟩ => ⟨⟨hp,s19,t19⟩,s19,t19,s20,t20⟩)
    (fun _ _ ⟨⟨e,hp⟩,rest⟩ => ⟨e,hp,rest⟩))
  apply RelCT.exists_
  intro e
  rw [List.append_assoc]
  apply RelCT.block_append
  rw [←hL.n]
  have cp := copyPoint_relCT (base:=base) (E:=e) hL.lay hAl rs
    (V:=[K.E.x,K.E.y,K.E.z,K.D.x,K.D.y,K.D.z]++jacTreeLive K m)
    (fun x hx => by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind) hc.copyStep
  apply RelCT.seq (relCT_keepControls cp hcopy)
  apply RelCT.block_append
  have st := jacStore_relCT (base:=base) (a:=m+1) (E:=copyPointEnv e K.R K.D)
    (V:=[K.R.x,K.R.y,K.R.z]++([K.E.x,K.E.y,K.E.z,K.D.x,K.D.y,K.D.z]++jacTreeLive K m))
    hL.lay hL.n hL.rxy hL.rxz (hAl.sl _ (rs _ (by simp [jacCoords])))
    (jacTblPt_mem K (by omega) (by omega)) (fun _ hx => List.mem_append_left _ hx)
    (by simpa only [Nat.add_sub_cancel] using sep) hc.store
  have sk := relCT_keepControls (a:=BitVec.ofNat 64 (16-m)) (b:=off base (K.tbl+96*m)) st
    (fun r hr => tableStore_preserves K (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> decide))
  apply RelCT.seq (sk.mono
    (Q':=fun (s t : State) => ∃ e, FieldPair K.M base size C.p (·∈jacWinSlots K)
      (jacCoords (Jacobian.tablePt K (m+1))++([K.R.x,K.R.y,K.R.z]++
        ([K.E.x,K.E.y,K.E.z,K.D.x,K.D.y,K.D.z]++jacTreeLive K m))) e s t ∧
      s.gpr .x19=BitVec.ofNat 64 (16-m) ∧ t.gpr .x19=BitVec.ofNat 64 (16-m) ∧
      s.gpr .x20=off base (K.tbl+96*m) ∧ t.gpr .x20=off base (K.tbl+96*m))
    (fun _ _ ⟨hp,s19,t19,s20,t20⟩ => ⟨⟨hp,by simpa only [Nat.add_sub_cancel] using s20,
      by simpa only [Nat.add_sub_cancel] using t20⟩,s19,t19,s20,t20⟩)
    (fun _ _ ⟨⟨e,hp⟩,rest⟩ => ⟨e,hp,rest⟩))
  apply RelCT.exists_
  intro et
  have adv := keepsField_relCT (M:=K.M) (base:=base) (size:=size) (m:=C.p)
    (Sl:=(·∈jacWinSlots K)) (E:=et)
    (V:=jacCoords (Jacobian.tablePt K (m+1))++([K.R.x,K.R.y,K.R.z]++
      ([K.E.x,K.E.y,K.E.z,K.D.x,K.D.y,K.D.z]++jacTreeLive K m)))
    (Pre:=fun s => s.gpr .x19=BitVec.ofNat 64 (16-m) ∧ s.gpr .x20=off base (K.tbl+96*m))
    (Post:=fun s => s.gpr .x19=BitVec.ofNat 64 (16-(m+1)) ∧ s.gpr .x20=off base (K.tbl+96*(m+1)))
    (by decide : Reg.x0∉[Reg.x19,Reg.x20]) hc.advance
    (fun s t hp ps pt => ⟨hp.sp,fun r hr => by
      simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact ps.1.trans pt.1.symm
      · exact ps.2.trans pt.2.symm⟩)
    (fun s _ hp => WP.mono (jacAdvanceTable_ok hp.1 hp.2 hm15) (fun _ ⟨hc,hp,hk⟩ => ⟨⟨hc,hp⟩,hk⟩))
  exact adv.mono (fun _ _ ⟨hp,s19,t19,s20,t20⟩ => ⟨hp,⟨s19,s20⟩,⟨t19,t20⟩⟩)
    (fun _ _ ⟨hp,ps,pt⟩ => ⟨et,hp.sub (by
      intro x hx
      have hv := jacTreeLive_next K hm1 x hx
      simpa only [jacCoords,List.append_assoc] using hv),ps.1,pt.1,ps.2,pt.2⟩)

/-- Every table-building branch and address is determined by public paired fields. -/
theorem jacTree_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (ht : K.tbl<4096) (hOne : K.one<C.p)
    (hc : JacTreeChecks K)
    (hcopy : ∀ r∈[Reg.x19,Reg.x20], ∀ i∈instrs (.block (copyPt K.M.n K.R K.D) : Prog isa), dstOf i≠some r)
    {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (·∈jacWinSlots K) (winRo K) E)
      (Jacobian.jacBuildTree K 16)
      (fun s t => ∃ E', FieldPair K.M base size C.p (·∈jacWinSlots K) (jacLive K) E' s t) := by
  let I := fun j s t => 1≤j ∧ j≤15 ∧ TreePair K C base size (16-j) s t
  have step : ∀ j, RelCT isa (I j) (Jacobian.jacTreeStep K 16) (fun s t =>
      eval (.nonzero .x .x19) s=eval (.nonzero .x .x19) t ∧
      (eval (.nonzero .x .x19) s=some false → ∃ E', FieldPair K.M base size C.p
        (·∈jacWinSlots K) (jacLive K) E' s t) ∧
      (eval (.nonzero .x .x19) s=some true → ∃ n<j, I n s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hj15 : j≤15
      · refine (jacTree_step_relCT hL hJ hAl hm ht hOne (m:=16-j) (by omega) (by omega) hc hcopy).mono
          (P':=I j) (fun _ _ h => h.2.2) ?_
        intro s t hp
        have hp' := hp
        obtain ⟨e,p,s19,t19,s20,t20⟩ := hp
        have cn : 16-(16-j+1)=j-1 := by omega
        rw [cn] at s19 t19
        refine ⟨by simp only [eval,State.read,s19,t19],fun he => ?_,fun he => ?_⟩
        · have hz : j-1=0 := by
            by_contra hn
            have hb : (BitVec.ofNat 64 (j-1) != 0)=true := by
              rw [bne_iff_ne]
              intro hh
              have hh' := congrArg BitVec.toNat hh
              simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : j-1<2^64)] at hh'
              exact hn hh'
            have htrue : eval (.nonzero .x .x19) s=some true := by
              change some (s.read .x .x19 != 0)=some true
              rw [read_x,s19,hb]
            rw [htrue] at he; cases he
          have hx : 16-j+1=16 := by omega
          rw [hx,jacTreeLive_full] at p
          exact ⟨e,p⟩
        · have hz : j-1≠0 := by
            intro hz; simp only [eval,State.read,s19,hz] at he; cases he
          refine ⟨j-1,by omega,by omega,by omega,?_⟩
          have hx : 16-j+1=16-(j-1) := by omega
          exact hx ▸ hp'
      · exact RelCT.of_false (fun _ _ h => hj15 h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  unfold Jacobian.jacBuildTree
  apply RelCT.seq (jacTree_init_relCT hL hAl ht hc)
  exact (RelCT.loop I step 15).mono (fun _ _ ⟨e,p,s19,t19,s20,t20⟩ =>
    ⟨by decide,by decide,e,p,s19,t19,by simpa only [Nat.mul_one] using s20,
      by simpa only [Nat.mul_one] using t20⟩) (fun _ _ h => h)

end VG.Proof.Weierstrass.AArch64
