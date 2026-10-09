import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsEntry
import VerifiedGarbage.Proof.Framework.ConstMem

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

private theorem joined_left (F I : List (BitVec 64)) (hf : F.length=488) (hi : I.length=488)
    {j : Nat} (hj : j<488) :
    (constMem 1048576 (F++I)).readW (1048576+BitVec.ofNat 64 (8*j)) 64=F.getD j 0 := by
  rw [constMem_held _ _ (by rw [List.length_append,hf,hi]; decide) j (by rw [List.length_append,hf,hi]; omega)]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left (by omega : j<F.length)]

private theorem joined_right (F I : List (BitVec 64)) (hf : F.length=488) (hi : I.length=488)
    {j : Nat} (hj : j<488) :
    (constMem 1048576 (F++I)).readW (1052480+BitVec.ofNat 64 (8*j)) 64=I.getD j 0 := by
  have ha : (1052480+BitVec.ofNat 64 (8*j) : Addr)=1048576+BitVec.ofNat 64 (8*(488+j)) := by
    rw [Nat.mul_add,BitVec.ofNat_add,← BitVec.add_assoc]
    rfl
  rw [ha,constMem_held _ _ (by rw [List.length_append,hf,hi]; decide) (488+j)
    (by rw [List.length_append,hf,hi]; omega)]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : F.length≤488+j),hf,Nat.add_sub_cancel_left]

def optimizedSignSatWith (p : Params) (m : Mem) : State :=
  { signSat p with
    mem := m
    syms := fun name=>if name="VG_MLDSA_NTT_EXPANDED" then 1048576 else 1052480
    rd := (signSat p).rd++[⟨1048576,3904⟩,⟨1052480,3904⟩] }

theorem staticRoots_pre {p : Params} {S : Nat} {s : State} (hS : 0<S)
    (hk : (signK p S).pre s) (hr : StaticRoots S s)
    (hrd : s.rd=[⟨s.gpr .x0,p.skLen⟩,⟨s.gpr .x1,64⟩,⟨s.gpr .x2,32⟩] ++
      [⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩]) :
    (signContractT p (abi.withConsts signRootConsts) S).pre s := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hS)
  dsimp only [signK,scrLen] at hk
  rw [Nat.mul_comm 8 (scratchWords p)] at hk
  obtain ⟨_,hw,d1,d2,d3,d4,d5,d6,d7,k1,k2,k3,k4,k5,n1,n2,n3,n4,n5,hsp⟩ := hk
  sig_pre [signContractT,signSig,abi,argRegs,Abi.withConsts,signRootConsts_eq,
    nttConsts_eq,Inverse.inverseConsts_eq,Abi.constRegions,Abi.constsHeld,
    TableConstants.staticNttWords_length,InverseTable.expandedWords_length,stackBelow]
  refine ⟨hsp,?_,hr.forward.held,hr.inverse.held,hr.forward.fit,hr.forward.writable,
    hr.forward.stack,hr.inverse.fit,hr.inverse.writable,hr.inverse.stack,?_,hw,
    d1,d2,d3,d4,d5,d6,d7,k1,k2,k3,k4,k5,n1,n2,n3,n4,n5⟩
  · rw [hrd]; rfl
  · rw [hrd]; rfl

theorem optimizedSignSatWith_pre (p : Params) (hp : Ok3 p) (m : Mem)
    (hf : ∀j<488,m.readW (1048576+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD j 0)
    (hi : ∀j<488,m.readW (1052480+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD j 0) :
    (signContractT p (abi.withConsts signRootConsts) signStack).pre (optimizedSignSatWith p m) := by
  apply staticRoots_pre (by decide)
  · rcases hp with rfl|rfl|rfl
    all_goals dsimp [signK,scrLen,optimizedSignSatWith,signSat]
    all_goals refine ⟨List.subset_append_left _ _, ?_⟩
    all_goals sig_and_intros
    all_goals first | rfl | exact Region.disjoint_of_sep (by decide) | decide
  · refine ⟨⟨hf,by dsimp [optimizedSignSatWith]; decide,?_,?_,by dsimp [optimizedSignSatWith,signSat]; exact Region.disjoint_of_sep (by decide)⟩,
      ⟨hi,by dsimp [optimizedSignSatWith]; decide,?_,?_,by dsimp [optimizedSignSatWith,signSat]; exact Region.disjoint_of_sep (by decide)⟩⟩
    · apply Covers.one
      exact ⟨⟨1048576,3904⟩,by simp [optimizedSignSatWith],Region.contains_self _ _⟩
    · rcases hp with rfl|rfl|rfl
      all_goals dsimp [optimizedSignSatWith,signSat]
      all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      all_goals sig_and_intros
      all_goals first | rfl | exact Region.disjoint_of_sep (by decide) | decide
    · apply Covers.one
      exact ⟨⟨1052480,3904⟩,by simp [optimizedSignSatWith],Region.contains_self _ _⟩
    · rcases hp with rfl|rfl|rfl
      all_goals dsimp [optimizedSignSatWith,signSat]
      all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      all_goals sig_and_intros
      all_goals first | rfl | exact Region.disjoint_of_sep (by decide) | decide
  · rfl

def optimizedSignSat (p : Params) : State := optimizedSignSatWith p
  (constMem 1048576 (Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords++
    Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords))

theorem optimizedSign_sat {p : Params} (hp : Ok3 p) :
    (signContractT p (abi.withConsts signRootConsts) signStack).pre (optimizedSignSat p) := by
  apply optimizedSignSatWith_pre p hp
  · intro j hj; exact joined_left _ _ TableConstants.staticNttWords_length InverseTable.expandedWords_length hj
  · intro j hj; exact joined_right _ _ TableConstants.staticNttWords_length InverseTable.expandedWords_length hj

end VG.Proof.MlDsa.AArch64.Sign
