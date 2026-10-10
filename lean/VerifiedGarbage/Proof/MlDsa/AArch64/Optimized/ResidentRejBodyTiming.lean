import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejProbePublic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejChoiceTiming
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ## From `ResidentRejFourTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def FourPublic (s t : State) : Prop :=
  Constants s ∧ Constants t ∧ CandidatesEq s t 4 ∧
  InRegions (s.rd++s.wr) (s.gpr .x2) 16 ∧ InRegions (t.rd++t.wr) (t.gpr .x2) 16 ∧
  VG.AArch64.Taint.Agree (Taint.ofRegs [.x2,.x3,.x4,.x9]) s t

theorem fourStep_relCT : RelCT isa FourPublic
    (.seq (.block vectorTry) (.ite (.zero .x .x6) (.block vectorAccept) (.block vectorReject)))
    (fun _ _ => True) := by
  intro s t tr ur s' t' hp es et
  obtain ⟨cs,ct,hcand,rs,rt,hpub⟩ := hp
  cases es with
  | seq ep ec =>
    cases et with
    | seq fp fc =>
      have hx (r : Reg) (hr : r∈[Reg.x2,.x3,.x4,.x9]) : s.gpr r=t.gpr r :=
        hpub.2 r (by simpa only [Taint.ofRegs,RegSet.mem_ofList] using hr)
      have htr := vectorTry_ct _ _ _ _ _ _ trivial trivial
        ⟨hpub.1,fun r hr => hx r (by
          simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_singleton] at hr
          subst r; simp)⟩ ep fp
      obtain ⟨_,a,ea,ha,ma,va,da,fa⟩ := vectorTry_ok rs cs.index
      obtain ⟨_,b,eb,hb,mb,vb,db,fb⟩ := vectorTry_ok rt ct.index
      have hd := fourDecoded_eq cs ct hcand
      have hf : a.gpr .x6=b.gpr .x6 := by
        rw [fa,fb,hd,modulusVector_eq cs ct,cs.ones,ct.ones]
      obtain ⟨_,rfl⟩ := Exec.det ep ea
      obtain ⟨_,rfl⟩ := Exec.det fp eb
      have hc := fourChoice_ct _ _ _ _ _ _ trivial trivial ?_ ec fc
      · exact ⟨by rw [htr,hc],trivial⟩
      · refine ⟨⟨ha.sp.trans (hpub.1.trans hb.sp.symm),?_⟩,?_⟩
        · intro r hr
          simp only [choicePublic,Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [ha.get .x3,hb.get .x3]; exact hx .x3 (by simp)
          · rw [ha.get .x4,hb.get .x4]; exact hx .x4 (by simp)
          · exact hf
          · rw [ha.get .x9,hb.get .x9]; exact hx .x9 (by simp)
        · intro v hv
          simp only [choicePublic,RegSet.mem_ofList,List.mem_singleton] at hv
          subst v
          rw [da,db,hd]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejWideTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def WidePublic (s t : State) : Prop :=
  Constants s ∧ Constants t ∧ CandidatesEq s t 16 ∧
  (∀j<4,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16) ∧
  (∀j<4,InRegions (t.rd++t.wr) (t.gpr .x2+BitVec.ofNat 64 (12*j)) 16) ∧
  VG.AArch64.Taint.Agree (Taint.ofRegs [.x2,.x3,.x4,.x9]) s t

theorem wideStep_relCT : RelCT isa WidePublic
    (.seq (.block wideTry) (.ite (.zero .x .x6) (.block wideAccept) (.block wideReject)))
    (fun _ _ => True) := by
  intro s t tr ur s' t' hp es et
  obtain ⟨cs,ct,hcand,rs,rt,hpub⟩ := hp
  cases es with
  | seq ep ec =>
    cases et with
    | seq fp fc =>
      have hx (r : Reg) (hr : r∈[Reg.x2,.x3,.x4,.x9]) : s.gpr r=t.gpr r :=
        hpub.2 r (by simpa only [Taint.ofRegs,RegSet.mem_ofList] using hr)
      have htr := wideTry_ct _ _ _ _ _ _ trivial trivial
        ⟨hpub.1,fun r hr => hx r (by
          simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_singleton] at hr
          subst r; simp)⟩ ep fp
      obtain ⟨_,a,ea,haf,da,fa⟩ := wideTry_ok cs.index rs
      have ha := haf.only
      obtain ⟨_,b,eb,hbf,db,fb⟩ := wideTry_ok ct.index rt
      have hb := hbf.only
      have hd := quarterMask_eq cs ct hcand
      have hf : a.gpr .x6=b.gpr .x6 := by
        rw [fa,fb,hd,cs.ones,ct.ones]
      obtain ⟨_,rfl⟩ := Exec.det ep ea
      obtain ⟨_,rfl⟩ := Exec.det fp eb
      have hc := wideChoice_ct _ _ _ _ _ _ trivial trivial ?_ ec fc
      · exact ⟨by rw [htr,hc],trivial⟩
      · refine ⟨⟨ha.sp.trans (hpub.1.trans hb.sp.symm),?_⟩,?_⟩
        · intro r hr
          simp only [choicePublic,Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [ha.get .x3,hb.get .x3]; exact hx .x3 (by simp)
          · rw [ha.get .x4,hb.get .x4]; exact hx .x4 (by simp)
          · exact hf
          · rw [ha.get .x9,hb.get .x9]; exact hx .x9 (by simp)
        · intro v hv
          simp only [choicePublic,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] at hv
          have hh (j : Nat) (hj : j<4) := (da j hj).trans ((quarterValues_eq cs ct hcand hj).trans (db j hj).symm)
          rcases hv with rfl | rfl | rfl | rfl
          · exact hh 0 (by decide)
          · exact hh 1 (by decide)
          · exact hh 2 (by decide)
          · exact hh 3 (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejBodyTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem keep_sp {P : State → State → Prop} {c : Prog isa}
    (h : RelCT isa P c (fun _ _ => True)) (hp : ∀s t,P s t → s.sp=t.sp) :
    RelCT isa P c (fun s t => s.sp=t.sp) := by
  intro s t tr ur s' t' hab es et
  exact ⟨(h _ _ _ _ _ _ hab es et).1,(AArch64.Exec.sp es).trans ((hp _ _ hab).trans (AArch64.Exec.sp et).symm)⟩

theorem fourBody_relCT : RelCT isa FourPublic vectorBody (fun _ _ => True) := by
  unfold vectorBody
  apply RelCT.assoc
  apply RelCT.seq (keep_sp fourStep_relCT (fun _ _ h => h.2.2.2.2.2.1))
  exact RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ h => ⟨h,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩) (by taint_decide)

theorem wideBody_relCT : RelCT isa WidePublic wideBody (fun _ _ => True) := by
  unfold wideBody
  apply RelCT.assoc
  apply RelCT.seq (keep_sp wideStep_relCT (fun _ _ h => h.2.2.2.2.2.1))
  exact RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ h => ⟨h,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
