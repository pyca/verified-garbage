import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejProbePublic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejChoiceTiming

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
