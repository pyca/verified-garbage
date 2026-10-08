import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingInit

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

theorem nafTable_step_relCT {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat}
    (hL : NafLay K size) (hJ : 1≤K.J ∧ 4*K.J≤64*K.M.n+4) (hm : UnitMod C.p (2^(64*K.M.n)))
    (ht : K.tbl<2^31) (hOne : K.one<C.p) (hm8 : m<8) (hc : NafTableChecks K) :
    RelCT isa (NafTablePair K C base size m) (Naf.tableStep K).inline
      (fun s t => NafTablePair K C base size (m+1) s t ∧
        s.cf=some (decide (m+1<8)) ∧ t.cf=some (decide (m+1<8))) := by
  have rs : ∀ x∈jacCoords K.R,x∈nafSlots K := by
    intro x hx
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have sep : K.R.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.R.x := by
    have hx := hL.tbl K.R.x (by simp [winOther])
    have hz := hL.tbl K.R.z (by simp [winOther])
    rw [hL.rxz] at hz
    omega
  have slots : ∀ x∈rcbW K.S K.D++rcbR K.S K.R (Naf.twice K),x∈nafSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ hx))
    · have he : x∈winRo K++winOther K ∨ x∈jacCoords (Naf.twice K) := by
        simp only [rcbR,winRo,winOther,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
        grind
      exact he.elim (List.mem_append_left _) (nafTblPt_mem K (by decide) (by decide) x)
  unfold NafTablePair
  apply RelCT.exists_
  intro E
  unfold Naf.tableStep
  simp only [Code.inline]
  have ac := jacAdd_relCT (base:=base) (E:=E) hL.lay hm hc.add (hL.rcbApart_twice hJ)
    slots (nafTableLive_read K m) hOne
  apply RelCT.seq ((relCT_keepGprS (v:=BitVec.ofNat 64 m) ac hc.keepAdd).mono
    (Q':=fun (s t : State) => ∃ e, FieldPair K.M base size C.p (·∈nafSlots K)
      (jacCoords K.D++nafTableLive K m) e s t ∧
      s.gpr .rbx=BitVec.ofNat 64 m ∧ t.gpr .rbx=BitVec.ofNat 64 m)
    (fun _ _ h => h) (fun _ _ ⟨⟨e,p⟩,rest⟩ => ⟨e,p,rest⟩))
  apply RelCT.exists_
  intro e
  rw [List.append_assoc]
  apply RelCT.block_append
  have cp := copyPoint_relCT (base:=base) (E:=e) hL.lay rs
    (V:=jacCoords K.D++nafTableLive K m) (fun _ hx => List.mem_append_left _ hx) hc.copyStep
  apply RelCT.seq (relCT_keepGpr cp hc.keepCopy)
  apply RelCT.block_append
  apply RelCT.seq (nafTableStore_relCT (base:=base) (j:=m) (E:=copyPointEnv e K.R K.D)
    hL.lay hL.n hL.rxy hL.rxz hm8 ht (by have := hL.table_le; omega)
    (nafTblPt_mem K (by omega) (by omega)) (fun _ hx => List.mem_append_left _ hx) sep hc.store)
  have adv := keepsField_relCT (M:=K.M) (base:=base) (size:=size) (m:=C.p)
    (Sl:=(·∈nafSlots K))
    (V:=jacCoords (K.tblPt (m+1))++(jacCoords K.R++(jacCoords K.D++nafTableLive K m)))
    (E:=pointTransferEnv (copyPointEnv e K.R K.D) (K.tblPt (m+1)) K.R)
    (Pre:=fun s => s.gpr .rbx=BitVec.ofNat 64 m)
    (Post:=fun s => s.gpr .rbx=BitVec.ofNat 64 (m+1) ∧ s.cf=some (decide (m+1<8)))
    (by decide : Reg.rdi∉[Reg.rbx]) hc.advance
    (fun _ _ _ ps pt => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ps.trans pt.symm))
    (fun _ _ hp => WP.mono (nafTable_advance_ok hm8 hp) (fun _ ⟨ct,cf,hk⟩ => ⟨⟨ct,cf⟩,hk⟩))
  exact adv.mono (fun _ _ h => h) (fun _ _ ⟨p,ps,pt⟩ =>
    ⟨⟨_,p.sub (by
      intro x hx
      simpa only [List.append_assoc] using nafTableLive_next K m x hx),ps.1,pt.1⟩,ps.2,pt.2⟩)

end VG.Proof.Weierstrass.X86_64
