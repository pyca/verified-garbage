import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableCopy
import VerifiedGarbage.Proof.Weierstrass.AArch64.ArithmeticAddTiming
import VerifiedGarbage.Impl.Weierstrass.AArch64.ArithmeticTable
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableInit
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableTiming

/-! ## `ArithmeticTableStep` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem arithmeticTable_step_ok (certs : Forward.Arithmetic.Cases) {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hsize : 8192≤size) (hC : Law C) (ha : AM3 C)
    (hOne : K.one<C.p) {P : Point C} (hP : onCurve C P=true)
    (hm1 : 1≤m) (hm7 : m≤7) {s₀ s : State} (hI : NafTableInv K C base size P s₀ s m) :
    WP isa (ArithmeticTable.tableStep K) s fun t => NafTableInv K C base size P s₀ t (m+1) := by
  have hf := hI.field
  have hv := nafTableLive_read K m
  have ds : ∀ x∈rcbW K.S K.D ++ rcbR K.S K.R (Naf.twice K), x∈jacWinSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ hx))
    · have he : x∈winRo K ++ winOther K ∨ x∈jacCoords (Naf.twice K) := by
        simp only [rcbR,winRo,winOther,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
        grind
      rcases he with he | he
      · exact List.mem_append_left _ he
      · exact jacTblPt_mem K (by decide) (by decide) x he
  unfold ArithmeticTable.tableStep
  apply WP.seq
  refine WP.mono (arithmeticAdd_ok certs hL.lay hAl (callOf_small (Nat.le_of_eq hL.n)) hm hsize hC ha (hL.rcbApart_twice hJ) ds hf hv hOne
    (hC.onCurve_mul hP _) (hC.onCurve_mul hP _) hI.point hI.twice) fun u ⟨eu,ka,iu,ju⟩ => ?_
  have jw : InvJ C (eu K.D.x) (eu K.D.y) (eu K.D.z) (mul (2*(m+1)-1) P) := by
    rw [hC.add_mul_mul hP,show 2*m-1+2=2*(m+1)-1 by omega] at ju
    exact ju
  have ka := ka.mono (W' := winOther K) (fun _ hx => List.mem_append_right _ hx)
  have pu : u.gpr .x20=off base (K.tbl+96*((m+1)-1)) := by
    rw [ka.gpr _ (by rw [hL.n]; decide),hI.pointer,Nat.add_sub_cancel]
  have vd : ∀ x∈rcbR K.S K.D K.D, x∈jacCoords K.D++nafTableLive K m := by
    intro x hx
    have hsa := hv K.S.a (by simp [rcbR])
    have hsb := hv K.S.b3 (by simp [rcbR])
    simp only [rcbR,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  rw [WP.block_append_iff]
  refine WP.mono (jacTreeCopyStore_ok hL hAl (by omega) (by omega) iu vd pu jw)
    fun v ⟨ks,iv,jr,jnew⟩ => ?_
  let W := winOther K ++ jacCoords (Jacobian.tablePt K (m+1))
  have kas : ProgKeep K.M base W s v := (ka.mono (fun _ hx => List.mem_append_left _ hx)).trans ks
  have p19 : v.gpr .x19=BitVec.ofNat 64 (8-m) := by
    rw [kas.gpr _ (by rw [hL.n]; decide),hI.counter]
  have p20 : v.gpr .x20=off base (K.tbl+96*m) := by
    rw [kas.gpr _ (by rw [hL.n]; decide),hI.pointer]
  refine WP.mono (nafAdvance_ok p19 p20 hm7) fun t ⟨hc,hp,kc⟩ => ?_
  have it := (iv.of_keeps kc (by decide)).to_tmv.sub (nafTableLive_next K hm1)
  have slots : ∀ x∈W, x∈jacWinSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (List.mem_append_right _ hx)
    · exact jacTblPt_mem K (by omega) (by omega) x hx
  have kct : KeepRegs (jacTreeClob K) v t := (Keeps.regs kc).mono (fun _ hx => List.mem_append_right _ hx)
  have kst : KeepRegs (jacTreeClob K) s t :=
    (KeepRegs.mono ⟨kas.gpr,kas.rd,kas.wr,kas.sp⟩ (fun _ hx => List.mem_append_left _ hx)).trans kct
  have uw : Unch base (jacTreeWrites K) s.mem t.mem := by
    rw [kc.mem]
    apply kas.unch.mono
    intro w hw
    simp only [jacTreeWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw ⊢
    rcases hw with ⟨x,hx,rfl⟩ | rfl
    · refine Or.inl ⟨x,?_,rfl⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · apply List.mem_append_right
        have hh := jacTblPt_mem K (by omega : 1≤m+1) (by omega : m+1≤16) x hx
        simp only [Jacobian.tablePt,jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact jacTbl_mem K (by omega) (by omega) (c:=0) (by decide)
        · exact jacTbl_mem K (by omega) (by omega) (c:=1) (by decide)
        · exact jacTbl_mem K (by omega) (by omega) (c:=2) (by decide)
    · exact Or.inr rfl
  have beq (x : Nat) (hx : x∈jacCoords (Naf.twice K)) : tmv C K.M.n base t x=tmv C K.M.n base s x := by
    unfold tmv; rw [kc.mem]
    rw [kas.slot hL.lay hf.scr slots (jacTblPt_mem K (by decide) (by decide) x hx) ?_]
    intro hw
    rcases List.mem_append.mp hw with hw | hw
    · have sep := hL.tbl x (List.mem_append_right _ hw)
      simp only [jacCoords,Naf.twice,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx
      omega
    · simp only [jacCoords,Naf.twice,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx hw
      omega
  refine ⟨it,?_,?_,?_,hc,hp,hI.keep.trans kst,?_⟩
  · simpa only [tmv,kc.mem] using jr
  · rw [beq _ (by simp [jacCoords]),beq _ (by simp [jacCoords]),beq _ (by simp [jacCoords])]
    exact hI.twice
  · intro a ha1 ham
    by_cases he : a=m+1
    · subst a; simpa only [tmv,kc.mem] using jnew
    · have ham' : a≤m := by omega
      have teq (x : Nat) (hx : x∈jacCoords (Jacobian.tablePt K a)) :
          tmv C K.M.n base t x=tmv C K.M.n base s x := by
        unfold tmv; rw [kc.mem]
        rw [kas.slot hL.lay hf.scr slots (jacTblPt_mem K ha1 (by omega) x hx) ?_]
        intro hw
        rcases List.mem_append.mp hw with hw | hw
        · have sep := hL.tbl x (List.mem_append_right _ hw)
          simp only [jacCoords,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx
          omega
        · exact jacTable_ne ha1 ham' hx hw rfl
      rw [teq _ (by simp [jacCoords]),teq _ (by simp [jacCoords]),teq _ (by simp [jacCoords])]
      exact hI.table a ha1 ham'
  · exact (hI.unch.trans uw).mono (fun _ hw => (List.mem_append.mp hw).elim id id)

end VG.Proof.Weierstrass.AArch64

end

/-! ## `ArithmeticTable` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

/-- Build the eight odd multiples and the cached double. -/
theorem arithmeticTable_ok (certs : Forward.Arithmetic.Cases) {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hsize : 8192≤size) (hC : Law C) (ha : AM3 C)
    (ht : K.tbl<4096) (hOne : K.one<C.p) {P : Point C} (hP : onCurve C P=true)
    {s : State} (hI : Inv K.M base size C.p (·∈jacWinSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hJP : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) :
    WP isa (ArithmeticTable.table K) s (fun t => NafTableInv K C base size P s t 8) := by
  unfold ArithmeticTable.table
  apply WP.assoc
  refine WP.seq (WP.mono (nafTable_init_ok hL hJ hAl hm hC ha ht hP hI hJP) fun a ia => ?_)
  apply countLoop_ok (Inv := fun j t => NafTableInv K C base size P s t (8-j))
    (n := 7) (by decide)
  · intro j u hj hj7 hu
    refine WP.mono (arithmeticTable_step_ok certs hL hJ hAl hm hsize hC ha hOne hP (by omega) (by omega) hu)
      fun t it => ?_
    have he : 8-j+1=8-(j-1) := by omega
    refine ⟨he ▸ it,?_⟩
    have hc := it.counter
    have he' : 8-(8-j+1)=j-1 := by omega
    rwa [he'] at hc
  · intro t it; exact it
  · decide
  · exact ia

end VG.Proof.Weierstrass.AArch64

end

/-! ## `ArithmeticTableTimingStep` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

structure ArithmeticTableChecks (K : WinCfg) : Prop where
  base : NafTableChecks K
  add : ArithmeticAddChecks K K.R (Naf.twice K) K.D
  keepAdd : ∀ r∈[Reg.x19,Reg.x20],∀ i∈instrs (ArithmeticAdd.add K K.R (Naf.twice K) K.D),dstOf i≠some r

 theorem arithmeticTable_step_relCT (certs : Forward.Arithmetic.Cases) {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hsize : 8192≤size) (hOne : K.one<C.p)
    (hm1 : 1≤m) (hm7 : m≤7) (hc : ArithmeticTableChecks K)
    (hcopy : ∀ r∈[Reg.x19,Reg.x20], ∀ i∈instrs (.block (copyPt K.M.n K.R K.D) : Prog isa), dstOf i≠some r) :
    RelCT isa (NafTablePair K C base size m) (ArithmeticTable.tableStep K) (NafTablePair K C base size (m+1)) := by
  have rs : ∀ x∈jacCoords K.R, x∈jacWinSlots K := by
    intro x hx; apply List.mem_append_left
    simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have sep : K.R.x+96≤K.tbl+96*m ∨ K.tbl+96*m+96≤K.R.x := by
    have hx := hL.tbl K.R.x (by simp [winOther])
    have hz := hL.tbl K.R.z (by simp [winOther])
    rw [hL.rxz] at hz
    omega
  unfold NafTablePair
  apply RelCT.exists_
  intro E
  unfold ArithmeticTable.tableStep
  have slots : ∀ x∈rcbW K.S K.D ++ rcbR K.S K.R (Naf.twice K), x∈jacWinSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ hx))
    · have he : x∈winRo K ++ winOther K ∨ x∈jacCoords (Naf.twice K) := by
        simp only [rcbR,winRo,winOther,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
      exact he.elim (fun h => List.mem_append_left _ h) (jacTblPt_mem K (by decide) (by decide) x)
  have ac := arithmeticAdd_relCT certs (base:=base) (E:=E) hL.lay hAl (callOf_small (Nat.le_of_eq hL.n)) hm hsize (hL.rcbApart_twice hJ)
    slots (nafTableLive_read K m) hOne hc.add
  have ak := relCT_keepControls (a:=BitVec.ofNat 64 (8-m)) (b:=off base (K.tbl+96*m)) ac hc.keepAdd
  apply RelCT.seq (ak.mono
    (Q':=fun (s t : State) => ∃ e, FieldPair K.M base size C.p (·∈jacWinSlots K)
      ([K.D.x,K.D.y,K.D.z]++nafTableLive K m) e s t ∧
      s.gpr .x19=BitVec.ofNat 64 (8-m) ∧ t.gpr .x19=BitVec.ofNat 64 (8-m) ∧
      s.gpr .x20=off base (K.tbl+96*m) ∧ t.gpr .x20=off base (K.tbl+96*m))
    (fun _ _ h => h)
    (fun _ _ ⟨⟨e,hp⟩,rest⟩ => ⟨e,hp,rest⟩))
  apply RelCT.exists_
  intro e
  rw [List.append_assoc]
  apply RelCT.block_append
  rw [←hL.n]
  have cp := copyPoint_relCT (base:=base) (E:=e) hL.lay hAl rs
    (V:=[K.D.x,K.D.y,K.D.z]++nafTableLive K m)
    (fun x hx => by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind) hc.base.copyStep
  apply RelCT.seq (relCT_keepControls cp hcopy)
  apply RelCT.block_append
  have st := jacStore_relCT (base:=base) (a:=m+1) (E:=copyPointEnv e K.R K.D)
    (V:=[K.R.x,K.R.y,K.R.z]++([K.D.x,K.D.y,K.D.z]++nafTableLive K m))
    hL.lay hL.n hL.rxy hL.rxz (hAl.sl _ (rs _ (by simp [jacCoords])))
    (jacTblPt_mem K (by omega) (by omega)) (fun _ hx => List.mem_append_left _ hx)
    (by simpa only [Nat.add_sub_cancel] using sep) hc.base.store
  have sk := relCT_keepControls (a:=BitVec.ofNat 64 (8-m)) (b:=off base (K.tbl+96*m)) st
    (fun r hr => tableStore_preserves K (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> decide))
  apply RelCT.seq (sk.mono
    (Q':=fun (s t : State) => ∃ e, FieldPair K.M base size C.p (·∈jacWinSlots K)
      (jacCoords (Jacobian.tablePt K (m+1))++([K.R.x,K.R.y,K.R.z]++
        ([K.D.x,K.D.y,K.D.z]++nafTableLive K m))) e s t ∧
      s.gpr .x19=BitVec.ofNat 64 (8-m) ∧ t.gpr .x19=BitVec.ofNat 64 (8-m) ∧
      s.gpr .x20=off base (K.tbl+96*m) ∧ t.gpr .x20=off base (K.tbl+96*m))
    (fun _ _ ⟨hp,s19,t19,s20,t20⟩ => ⟨⟨hp,by simpa only [Nat.add_sub_cancel] using s20,
      by simpa only [Nat.add_sub_cancel] using t20⟩,s19,t19,s20,t20⟩)
    (fun _ _ ⟨⟨e,hp⟩,rest⟩ => ⟨e,hp,rest⟩))
  apply RelCT.exists_
  intro et
  have adv := keepsField_relCT (M:=K.M) (base:=base) (size:=size) (m:=C.p)
    (Sl:=(·∈jacWinSlots K)) (E:=et)
    (V:=jacCoords (Jacobian.tablePt K (m+1))++([K.R.x,K.R.y,K.R.z]++
      ([K.D.x,K.D.y,K.D.z]++nafTableLive K m)))
    (Pre:=fun s => s.gpr .x19=BitVec.ofNat 64 (8-m) ∧ s.gpr .x20=off base (K.tbl+96*m))
    (Post:=fun s => s.gpr .x19=BitVec.ofNat 64 (8-(m+1)) ∧ s.gpr .x20=off base (K.tbl+96*(m+1)))
    (by decide : Reg.x0∉[Reg.x19,Reg.x20]) hc.base.advance
    (fun s t hp ps pt => ⟨hp.sp,fun r hr => by
      simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact ps.1.trans pt.1.symm
      · exact ps.2.trans pt.2.symm⟩)
    (fun s _ hp => WP.mono (nafAdvance_ok hp.1 hp.2 hm7) (fun _ ⟨hc,hp,hk⟩ => ⟨⟨hc,hp⟩,hk⟩))
  exact adv.mono (fun _ _ ⟨hp,s19,t19,s20,t20⟩ => ⟨hp,⟨s19,s20⟩,⟨t19,t20⟩⟩)
    (fun _ _ ⟨hp,ps,pt⟩ => ⟨et,hp.sub (by
      intro x hx
      have hv := nafTableLive_next K hm1 x hx
      simpa only [jacCoords,List.append_assoc] using hv),ps.1,pt.1,ps.2,pt.2⟩)


end VG.Proof.Weierstrass.AArch64

end

/-! ## `ArithmeticTableTiming` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

/-- Every table-building branch and address is determined by public paired fields. -/
theorem arithmeticTable_relCT (certs : Forward.Arithmetic.Cases) {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hsize : 8192≤size) (ht : K.tbl<4096) (hOne : K.one<C.p)
    (hc : ArithmeticTableChecks K)
    (hcopy : ∀ r∈[Reg.x19,Reg.x20], ∀ i∈instrs (.block (copyPt K.M.n K.R K.D) : Prog isa), dstOf i≠some r)
    {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (·∈jacWinSlots K) (winRo K) E)
      (ArithmeticTable.table K)
      (fun s t => ∃ E', FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E' s t) := by
  let I := fun j s t => 1≤j ∧ j≤7 ∧ NafTablePair K C base size (8-j) s t
  have step : ∀ j, RelCT isa (I j) (ArithmeticTable.tableStep K) (fun s t =>
      eval (.nonzero .x .x19) s=eval (.nonzero .x .x19) t ∧
      (eval (.nonzero .x .x19) s=some false → ∃ E', FieldPair K.M base size C.p
        (·∈jacWinSlots K) (nafLive K) E' s t) ∧
      (eval (.nonzero .x .x19) s=some true → ∃ n<j, I n s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hj7 : j≤7
      · refine (arithmeticTable_step_relCT certs hL hJ hAl hm hsize hOne (m:=8-j) (by omega) (by omega) hc hcopy).mono
          (P':=I j) (fun _ _ h => h.2.2) ?_
        intro s t hp
        have hp' := hp
        obtain ⟨e,p,s19,t19,s20,t20⟩ := hp
        have cn : 8-(8-j+1)=j-1 := by omega
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
          have hx : 8-j+1=8 := by omega
          rw [hx] at p
          exact ⟨e,p.sub (nafTableLive_full K)⟩
        · have hz : j-1≠0 := by
            intro hz; simp only [eval,State.read,s19,hz] at he; cases he
          refine ⟨j-1,by omega,by omega,by omega,?_⟩
          have hx : 8-j+1=8-(j-1) := by omega
          exact hx ▸ hp'
      · exact RelCT.of_false (fun _ _ h => hj7 h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  unfold ArithmeticTable.table
  apply RelCT.assoc
  apply RelCT.seq (nafTable_init_relCT hL hAl hJ hm ht hc.base)
  exact (RelCT.loop I step 7).mono (fun _ _ ⟨e,p,s19,t19,s20,t20⟩ =>
    ⟨by decide,by decide,e,p,s19,t19,by simpa only [Nat.mul_one] using s20,
      by simpa only [Nat.mul_one] using t20⟩) (fun _ _ h => h)

end VG.Proof.Weierstrass.AArch64

end
