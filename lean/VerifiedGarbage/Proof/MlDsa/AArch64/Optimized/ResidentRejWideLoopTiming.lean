import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBodyTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem wide_public {σ τ s t : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hd : d+16≤n)
    (ps : ParseInv σ b p n L d s) (pt : ParseInv τ b p n L d t) : WidePublic s t := by
  have hr {σ s : State} (hl : StreamLayout σ b p n) (h : ParseInv σ b p n L d s) :
      ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16 := by
    intro j hj
    rw [h.keep.rd,h.keep.wr,h.x2,Offset.add_add,show 3*d+12*j=3*(d+4*j) by omega]
    exact hl.read16 _ (by omega)
  have hp := ps.publicRegs hm hsp pt
  refine ⟨ps.constants,pt.constants,ps.candidates_eq hs ht hm pt hd,hr hs ps,hr ht pt,hp.1,?_⟩
  intro r hr'
  simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl
  · exact hp.2 .x2 (by simp)
  · exact hp.2 .x3 (by simp)
  · exact hp.2 .x4 (by simp)
  · exact BitVec.eq_of_toNat_eq (ps.constants.qreg.trans pt.constants.qreg.symm)

theorem wideLoopStep_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hd : d+16≤n)
    (hc : (parsed σ b L d).length+16≤256) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t ∧
        s.gpr .x17=16 ∧ t.gpr .x17=16)
      wideBody (fun s t => ParseInv σ b p n L (d+16) s ∧ ParseInv τ b p n L (d+16) t ∧
        s.gpr .x17=16 ∧ t.gpr .x17=16 ∧
        s.gpr .x16=(if 16≤256-(parsed σ b L (d+16)).length ∧ 16≤n-(d+16) then 16 else 0) ∧
        t.gpr .x16=s.gpr .x16) := by
  intro s t tr ur s' t' hp es et
  have htr := (wideBody_relCT _ _ _ _ _ _ (wide_public hs ht hm hsp hd hp.1 hp.2.1) es et).1
  obtain ⟨_,a,ea,ha,h17a,hga⟩ := wideLoopStep_ok hs hp.1 hp.2.2.1 hd hc
  obtain ⟨_,b,eb,hb,h17b,hgb⟩ := wideLoopStep_ok ht hp.2.1 hp.2.2.2 hd
    (by rw [← parsed_eq hm (by omega) L]; exact hc)
  obtain ⟨_,rfl⟩ := Exec.det es ea
  obtain ⟨_,rfl⟩ := Exec.det et eb
  refine ⟨htr,ha,hb,h17a,h17b,hga,?_⟩
  rw [hgb,hga,parsed_eq hm hd L]

theorem wideLoop_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hd : d+16≤n)
    (hc : (parsed σ b L d).length+16≤256) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t ∧
        s.gpr .x17=16 ∧ t.gpr .x17=16)
      (.loop wideBody (.nonzero .x .x16))
      (fun s t => ∃j,ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t ∧ j%4=d%4) := by
  let I := fun m s t => ∃j,j+16≤n ∧ (parsed σ b L j).length+16≤256 ∧ j%4=d%4 ∧ n-j=m ∧
    ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t ∧ s.gpr .x17=16 ∧ t.gpr .x17=16
  have hstep : ∀m,RelCT isa (I m) wideBody
      (fun s t => isa.eval (.nonzero .x .x16) s=isa.eval (.nonzero .x .x16) t ∧
        (isa.eval (.nonzero .x .x16) s=some false →
          ∃j,ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t ∧ j%4=d%4) ∧
        (isa.eval (.nonzero .x .x16) s=some true → ∃m'<m,I m' s t)) := by
    intro m s t tr ur s' t' hp es et
    obtain ⟨j,hj,hc',hjmod,rfl,hp⟩ := hp
    obtain ⟨htrace,ha,hb,h17a,h17b,hga,heq⟩ := wideLoopStep_relCT hs ht hm hsp hj hc' _ _ _ _ _ _ hp es et
    refine ⟨htrace,by rw [eval_nonzero,eval_nonzero,heq],fun _ => ⟨j+16,ha,hb,by omega⟩,?_⟩
    intro hcontinue
    have hnext : 16≤256-(parsed σ b L (j+16)).length ∧ 16≤n-(j+16) := by
      by_contra hn
      rw [eval_nonzero,hga,ite_eq_right hn] at hcontinue
      contradiction
    exact ⟨n-(j+16),by omega,j+16,by omega,by omega,by omega,rfl,ha,hb,h17a,h17b⟩
  exact (RelCT.loop I hstep (n-d)).mono
    (fun _ _ hp => ⟨d,hd,hc,rfl,rfl,hp⟩) (fun _ _ h => h)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
