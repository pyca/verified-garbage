import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBodyTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem four_public {σ τ s t : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hd : d+4≤n)
    (ps : ParseInv σ b p n L d s) (pt : ParseInv τ b p n L d t) : FourPublic s t := by
  have hp := ps.publicRegs hm hsp pt
  refine ⟨ps.constants,pt.constants,ps.candidates_eq hs ht hm pt hd,?_,?_,hp.1,?_⟩
  · rw [ps.keep.rd,ps.keep.wr,ps.x2]; exact hs.read16 _ (by omega)
  · rw [pt.keep.rd,pt.keep.wr,pt.x2]; exact ht.read16 _ (by omega)
  · intro r hr'
    simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact hp.2 .x2 (by simp)
    · exact hp.2 .x3 (by simp)
    · exact hp.2 .x4 (by simp)
    · exact BitVec.eq_of_toNat_eq (ps.constants.qreg.trans pt.constants.qreg.symm)

theorem fourLoopStep_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hd : d+4≤n)
    (hc : (parsed σ b L d).length+4≤256) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t ∧
        s.gpr .x17=4 ∧ t.gpr .x17=4)
      vectorBody (fun s t => ParseInv σ b p n L (d+4) s ∧ ParseInv τ b p n L (d+4) t ∧
        s.gpr .x17=4 ∧ t.gpr .x17=4 ∧
        s.gpr .x16=(if 4≤256-(parsed σ b L (d+4)).length then s.gpr .x5 else 0) ∧
        t.gpr .x16=s.gpr .x16) := by
  intro s t tr ur s' t' hp es et
  have htr := (fourBody_relCT _ _ _ _ _ _ (four_public hs ht hm hsp hd hp.1 hp.2.1) es et).1
  obtain ⟨_,a,ea,ha,h17a,hga⟩ := fourLoopStep_ok hs hp.1 hp.2.2.1 hd hc
  obtain ⟨_,b,eb,hb,h17b,hgb⟩ := fourLoopStep_ok ht hp.2.1 hp.2.2.2 hd
    (by rw [← parsed_eq hm (by omega) L]; exact hc)
  obtain ⟨_,rfl⟩ := Exec.det es ea
  obtain ⟨_,rfl⟩ := Exec.det et eb
  refine ⟨htr,ha,hb,h17a,h17b,hga,?_⟩
  have hx5 := (ha.publicRegs hm hsp hb).2 .x5 (by simp)
  rw [hgb,hga,parsed_eq hm hd L,hx5]

theorem fourLoop_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hd : d+4≤n) (hmod : d%4=n%4)
    (hc : (parsed σ b L d).length+4≤256) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t ∧
        s.gpr .x17=4 ∧ t.gpr .x17=4)
      (.loop vectorBody (.nonzero .x .x16))
      (fun s t => ∃j,ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t) := by
  let I := fun m s t => ∃j,j+4≤n ∧ (parsed σ b L j).length+4≤256 ∧ j%4=n%4 ∧ n-j=m ∧
    ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t ∧ s.gpr .x17=4 ∧ t.gpr .x17=4
  have hstep : ∀m,RelCT isa (I m) vectorBody
      (fun s t => isa.eval (.nonzero .x .x16) s=isa.eval (.nonzero .x .x16) t ∧
        (isa.eval (.nonzero .x .x16) s=some false →
          ∃j,ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t) ∧
        (isa.eval (.nonzero .x .x16) s=some true → ∃m'<m,I m' s t)) := by
    intro m s t tr ur s' t' hp es et
    obtain ⟨j,hj,hc',hmod',rfl,hp⟩ := hp
    obtain ⟨htrace,ha,hb,h17a,h17b,hga,heq⟩ := fourLoopStep_relCT hs ht hm hsp hj hc' _ _ _ _ _ _ hp es et
    refine ⟨htrace,by rw [eval_nonzero,eval_nonzero,heq],fun _ => ⟨j+4,ha,hb⟩,?_⟩
    intro hcontinue
    have hnext : 4≤256-(parsed σ b L (j+4)).length := by
      by_contra hn
      rw [eval_nonzero,hga,ite_eq_right hn] at hcontinue
      contradiction
    have h5 : (s'.gpr .x5).toNat≠0 := by
      intro hz
      have hx : s'.gpr .x5=0#64 := BitVec.eq_of_toNat_eq hz
      rw [eval_nonzero,hga,ite_eq_left hnext,hx] at hcontinue
      contradiction
    rw [ha.x5] at h5
    exact ⟨n-(j+4),by omega,j+4,by omega,by omega,by omega,rfl,ha,hb,h17a,h17b⟩
  exact (RelCT.loop I hstep (n-d)).mono
    (fun _ _ hp => ⟨d,hd,hc,hmod,rfl,hp⟩) (fun _ _ h => h)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
