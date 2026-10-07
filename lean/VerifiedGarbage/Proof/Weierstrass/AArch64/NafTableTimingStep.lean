import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableTimingInit
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

 def NafTablePair (K : WinCfg) (C : Curve) (base : Addr) (size m : Nat) (s t : State) : Prop :=
  ∃ E, FieldPair K.M base size C.p (·∈jacWinSlots K) (nafTableLive K m) E s t ∧
    s.gpr .x19=BitVec.ofNat 64 (8-m) ∧ t.gpr .x19=BitVec.ofNat 64 (8-m) ∧
    s.gpr .x20=off base (K.tbl+96*m) ∧ t.gpr .x20=off base (K.tbl+96*m)

 theorem nafTable_step_relCT {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    (hm1 : 1≤m) (hm7 : m≤7) (hc : NafTableChecks K)
    (hcopy : ∀ r∈[Reg.x19,Reg.x20], ∀ i∈instrs (.block (copyPt K.M.n K.R K.D) : Prog isa), dstOf i≠some r) :
    RelCT isa (NafTablePair K C base size m) (Naf.tableStep K) (NafTablePair K C base size (m+1)) := by
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
  unfold Naf.tableStep
  have slots : ∀ x∈rcbW K.S K.D ++ rcbR K.S K.R (Naf.twice K), x∈jacWinSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ hx))
    · have he : x∈winRo K ++ winOther K ∨ x∈jacCoords (Naf.twice K) := by
        simp only [rcbR,winRo,winOther,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
      exact he.elim (fun h => List.mem_append_left _ h) (jacTblPt_mem K (by decide) (by decide) x)
  have ac := jacAdd_relCT (base:=base) (E:=E) hL.lay hAl hm (hL.rcbApart_twice hJ)
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
    (fun x hx => by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind) hc.copyStep
  apply RelCT.seq (relCT_keepControls cp hcopy)
  apply RelCT.block_append
  have st := jacStore_relCT (base:=base) (a:=m+1) (E:=copyPointEnv e K.R K.D)
    (V:=[K.R.x,K.R.y,K.R.z]++([K.D.x,K.D.y,K.D.z]++nafTableLive K m))
    hL.lay hL.n hL.rxy hL.rxz (hAl.sl _ (rs _ (by simp [jacCoords])))
    (jacTblPt_mem K (by omega) (by omega)) (fun _ hx => List.mem_append_left _ hx)
    (by simpa only [Nat.add_sub_cancel] using sep) hc.store
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
    (by decide : Reg.x0∉[Reg.x19,Reg.x20]) hc.advance
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
