import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsPre
import VerifiedGarbage.Proof.Framework.ConstMem

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

def pairedSignSatWith (p : Params) (m : Mem) : State :=
  { signSat p with
    mem := m
    syms := fun name=>if name="VG_MLDSA_NTT_EXPANDED" then 1048576 else if name="VG_MLDSA_INV_FOLDED" then 1052480 else 1056384
    rd := (signSat p).rd++[⟨1048576,3904⟩,⟨1052480,3904⟩,⟨1056384,4096⟩] }

theorem pairedSignSatWith_pre (p : Params) (hp : Ok3 p) (m : Mem)
    (hf : ∀j<488,m.readW (1048576+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD j 0)
    (hi : ∀j<488,m.readW (1052480+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD j 0)
    (hr : ∀j<512,m.readW (1056384+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Paired.expandedWords.getD j 0) :
    (signContractT p (abi.withConsts pairedSignRootConsts) signStack).pre (pairedSignSatWith p m) := by
  apply pairedRoots_pre (by decide)
  · rcases hp with rfl|rfl|rfl
    all_goals dsimp [signK,scrLen,pairedSignSatWith,signSat]
    all_goals refine ⟨List.subset_append_left _ _, ?_⟩
    all_goals sig_and_intros
    all_goals first | rfl | exact Region.disjoint_of_sep (by decide) | decide
  · refine ⟨⟨hf,by dsimp [pairedSignSatWith]; decide,?_,?_,by dsimp [pairedSignSatWith,signSat]; exact Region.disjoint_of_sep (by decide)⟩,
      ⟨hi,by dsimp [pairedSignSatWith]; decide,?_,?_,by dsimp [pairedSignSatWith,signSat]; exact Region.disjoint_of_sep (by decide)⟩⟩
    · apply Covers.one
      exact ⟨⟨1048576,3904⟩,by simp [pairedSignSatWith],Region.contains_self _ _⟩
    · rcases hp with rfl|rfl|rfl
      all_goals dsimp [pairedSignSatWith,signSat]
      all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      all_goals sig_and_intros
      all_goals first | rfl | exact Region.disjoint_of_sep (by decide)
    · apply Covers.one
      exact ⟨⟨1052480,3904⟩,by simp [pairedSignSatWith],Region.contains_self _ _⟩
    · rcases hp with rfl|rfl|rfl
      all_goals dsimp [pairedSignSatWith,signSat]
      all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      all_goals sig_and_intros
      all_goals first | rfl | exact Region.disjoint_of_sep (by decide)
  · refine ⟨hr,by dsimp [pairedSignSatWith]; decide,?_,?_,by dsimp [pairedSignSatWith,signSat]; exact Region.disjoint_of_sep (by decide)⟩
    · apply Covers.one
      exact ⟨⟨1056384,4096⟩,by simp [pairedSignSatWith],Region.contains_self _ _⟩
    · rcases hp with rfl|rfl|rfl
      all_goals dsimp [pairedSignSatWith,signSat]
      all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      all_goals sig_and_intros
      all_goals first | rfl | exact Region.disjoint_of_sep (by decide)
  · rfl

private theorem joined_three (F I P : List (BitVec 64)) (hf : F.length=488) (hi : I.length=488)
    (hp : P.length=512) :
    (∀j<488,(constMem 1048576 (F++I++P)).readW (1048576+BitVec.ofNat 64 (8*j)) 64=F.getD j 0) ∧
    (∀j<488,(constMem 1048576 (F++I++P)).readW (1052480+BitVec.ofNat 64 (8*j)) 64=I.getD j 0) ∧
    (∀j<512,(constMem 1048576 (F++I++P)).readW (1056384+BitVec.ofNat 64 (8*j)) 64=P.getD j 0) := by
  have hl : (F++I++P).length=1488 := by simp only [List.length_append,hf,hi,hp]
  constructor
  · intro j hj
    rw [constMem_held _ _ (by rw [hl]; decide) j (by rw [hl]; omega)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left (by simp [hf,hi]; omega : j<(F++I).length),
      List.getElem?_append_left (by omega : j<F.length)]
  · constructor
    · intro j hj
      have ha : (1052480+BitVec.ofNat 64 (8*j) : Addr)=1048576+BitVec.ofNat 64 (8*(488+j)) := by
        rw [Nat.mul_add,BitVec.ofNat_add,← BitVec.add_assoc]; rfl
      rw [ha,constMem_held _ _ (by rw [hl]; decide) (488+j) (by rw [hl]; omega)]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left (by simp [hf,hi]; omega : 488+j<(F++I).length),
        List.getElem?_append_right (by omega : F.length≤488+j),hf,Nat.add_sub_cancel_left]
    · intro j hj
      have ha : (1056384+BitVec.ofNat 64 (8*j) : Addr)=1048576+BitVec.ofNat 64 (8*(976+j)) := by
        rw [Nat.mul_add,BitVec.ofNat_add,← BitVec.add_assoc]; rfl
      rw [ha,constMem_held _ _ (by rw [hl]; decide) (976+j) (by rw [hl]; omega)]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp [hf,hi] : (F++I).length≤976+j),
        List.length_append,hf,hi,show 488+488=976 from rfl,Nat.add_sub_cancel_left]

def pairedSignSat (p : Params) : State := pairedSignSatWith p
  (constMem 1048576 (Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords++
    Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords++Impl.MlDsa.AArch64.Optimized.Paired.expandedWords))

theorem pairedSign_sat {p : Params} (hp : Ok3 p) :
    (signContractT p (abi.withConsts pairedSignRootConsts) signStack).pre (pairedSignSat p) := by
  obtain ⟨hf,hi,hr⟩ := joined_three _ _ _ TableConstants.staticNttWords_length
    InverseTable.expandedWords_length PairedTable.expandedWords_length
  exact pairedSignSatWith_pre p hp _ hf hi hr

end VG.Proof.MlDsa.AArch64.Sign
