import VerifiedGarbage.Proof.Weierstrass.X86.NafTableTimingInit

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.X86 VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafTable_step_relCT {F : Spec.Weierstrass.Mont.Modulus} {wk : Nat} {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat}
    (hL : NafLay K size) (hW : WkOk F K.M C.p size wk (·∈nafSlots K)) (hJ : K.J=65) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hOne : K.one<C.p) (hm8 : m<8) (hc : NafTableChecks K F) :
    RelCT isa (NafTablePair K C base size m) (Naf.tableStep K F)
      (fun s t => NafTablePair K C base size (m+1) s t ∧
        s.cf=some (decide (m+1<8)) ∧ t.cf=some (decide (m+1<8))) := by
  have rs : ∀ x∈jacCoords K.R,x∈nafSlots K := by
    intro x hx
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have sep : K.R.x+96≤K.tbl ∨ K.tbl+768≤K.R.x := by
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
      exact he.elim (List.mem_append_left _) (nafTblPt_mem K hL.n (by decide) (by decide) x)
  unfold NafTablePair
  apply RelCT.exists_
  intro E
  unfold Naf.tableStep
  have ac := jacAdd_relCT (counter:=BitVec.ofNat 32 m) (base:=base) (E:=E) hL.lay hW hm hc.add (hL.rcbApart_twice hJ)
    slots (nafTableLive_read K m) hOne
  apply RelCT.seq ac
  apply RelCT.exists_
  intro e
  rw [List.append_assoc,←hL.n]
  apply RelCT.block_append
  have cp := copyPoint_relCT (counter:=BitVec.ofNat 32 m) (base:=base) (E:=e) hL.lay hW rs
    (V:=jacCoords K.D++nafTableLive K m) (fun _ hx => List.mem_append_left _ hx) hc.copyStep
  apply RelCT.seq cp
  apply RelCT.block_append
  apply RelCT.seq (nafTableStore_relCT (base:=base) (j:=m) (E:=copyPointEnv e K.R K.D)
    hL.lay hW hL.n hL.rxy hL.rxz hm8 (by have := hL.table_le; omega)
    (nafTblPt_mem K hL.n (by omega) (by omega)) (fun _ hx => List.mem_append_left _ hx) sep hc.store)
  have adv := keepsField_relCT (counter:=BitVec.ofNat 32 m) (counter':=BitVec.ofNat 32 (m+1))
    (M:=K.M) (base:=base) (size:=size) (m:=C.p) (Sl:=(·∈nafSlots K))
    (V:=jacCoords (K.tblPt (m+1))++(jacCoords K.R++(jacCoords K.D++nafTableLive K m)))
    (E:=pointTransferEnv (copyPointEnv e K.R K.D) (K.tblPt (m+1)) K.R)
    (Pre:=fun _ => True) (Post:=fun s => s.cf=some (decide (m+1<8)))
    (ws:=[.esi]) (by decide) hc.advance
    (fun _ _ hp _ _ => hp.pub.agree (by
      intro r hr
      rw [List.mem_singleton.mp hr]
      exact hp.count₁.trans hp.count₂.symm))
    (fun _ _ ct _ => WP.mono (nafTable_advance_ok hm8 ct) (fun _ ⟨ct,cf,hk⟩ => ⟨ct,cf,hk⟩))
  exact adv.mono (fun _ _ h => ⟨h,trivial,trivial⟩) (fun _ _ ⟨p,ps,pt⟩ =>
    ⟨⟨_,p.sub (by
      intro x hx
      simpa only [List.append_assoc] using nafTableLive_next K hL.n m x hx)⟩,ps,pt⟩)

end VG.Proof.Weierstrass.X86
