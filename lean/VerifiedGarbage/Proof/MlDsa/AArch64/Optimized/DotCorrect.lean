import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotContract

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.DotInverse

theorem dot_correct {count : Nat} (hn : 0<count) (hn7 : count≤7) (s : State) (hp : (dotK count).pre s) :
    ∃trace t,Exec isa (staticCode count) s trace t ∧ abiPreserved s t ∧ (dotK count).post s t := by
  obtain ⟨htr,ha,hb,hw,hsep,hoa,hob,ht,hfa,hfb⟩ := hp
  obtain ⟨tr,t,he,hk,_,_,hm⟩ := dotStaticCode_words_ok hn hn7 ht htr ha hb hw hsep
  have hv := dotInverseMem_field hn7
    (fun j hj => positiveReduced_iff.mp (hfa j hj)) (fun j hj => positiveReduced_iff.mp (hfb j hj))
    (fun j hj => hoa.sub_left (VG.Offset.sub_base _ (by omega)))
    (fun j hj => hob.sub_left (VG.Offset.sub_base _ (by omega)))
  rw [← hm] at hv
  exact ⟨tr,t,he,dotCoreKeep_abi hk,hv⟩

theorem dot_ct {count : Nat} (hc : count=4 ∨ count=5 ∨ count=7) :
    ConstantTime isa (dotK count).pre (dotK count).pub (staticCode count) := by
  have ct : ConstantTime isa (fun _ => True)
      (Taint.AgreeS ["VG_MLDSA_INV_FOLDED"] (Taint.ofRegs [.x0,.x1,.x2])) (staticCode count) := by
    rcases hc with rfl | rfl | rfl
    · exact dot4Inverse_ct
    · exact dot5Inverse_ct
    · exact dot7Inverse_ct
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply ct s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2.2.2.1 ?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2.1
  · intro name hn
    have he : name="VG_MLDSA_INV_FOLDED" := by simpa only [List.mem_singleton] using hn
    subst name; exact hp.2.2.2.2

theorem dot_pub {count : Nat} {s t : State}
    (h : (dotInverseContract count (abi.withConsts VG.Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts)).pub s t) :
    (dotK count).pub s t := by
  sig_pub [dotInverseContract,dotInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq] at h
  exact ⟨h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.1,h.2.1⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
