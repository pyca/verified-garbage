import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.StaticCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryTraversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Spec.MlDsa.PositiveNtt
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.NttTable
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableArtifact
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts

/-! ## From `NttContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def positiveNttK : Contract isa where
  pre s := expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED") ∈ s.rd++s.wr ∧
    outputRegion (s.gpr .x0) ∈ s.wr ∧
    (expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")).Disjoint (outputRegion (s.gpr .x0)) ∧
    ExpandedArtifact s.mem (s.syms "VG_MLDSA_NTT_EXPANDED") ∧ Reduced s.mem (s.gpr .x0)
  post s t := PositivePolyIs t.mem (s.gpr .x0) (ntt (polyAt s.mem (s.gpr .x0)))
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.sp=t.sp ∧
    s.syms "VG_MLDSA_NTT_EXPANDED"=t.syms "VG_MLDSA_NTT_EXPANDED"

theorem positiveNtt_correct (s : State) (hp : positiveNttK.pre s) :
    ∃ trace t, Exec isa staticNtt s trace t ∧ abiPreserved s t ∧ positiveNttK.post s t := by
  obtain ⟨htr,hw,hsep,ht,hred⟩ := hp
  obtain ⟨tr,t,he,hk,hf,hm⟩ := staticNtt_words_ok ht htr hw hsep
  have hv := nttMemory_field (m := s.mem) (p := s.gpr .x0) ⟨hred,rfl⟩
  rw [← hm] at hv
  refine ⟨tr,t,he,⟨?_,hk.sp,hk.vcs⟩,hv.bound,hv.value⟩
  intro r hr
  apply hk.gpr r
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem positiveNtt_ct : ConstantTime isa positiveNttK.pre positiveNttK.pub staticNtt := by
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply staticNtt_ct s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2.1 ?_,?_⟩
  · intro r hr
    have he : r=.x0 := by simpa only [List.mem_singleton] using hr
    subst r; exact hp.1
  · intro name hn
    have he : name="VG_MLDSA_NTT_EXPANDED" := by simpa only [List.mem_singleton] using hn
    subst name; exact hp.2.2

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `NttSat.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def nttSat : State where
  gpr r := if r=.x0 then 4096 else 0
  sp := 131072
  syms _ := 65536
  mem := constMem 65536 staticNttWords
  rd := [⟨65536,3904⟩]
  wr := [⟨4096,1024⟩]

theorem nttSat_held : ∀ i<488,
    nttSat.mem.readW (65536+BitVec.ofNat 64 (8*i)) 64=staticNttWords.getD i 0 := by
  intro i hi
  dsimp only [nttSat]
  exact constMem_held 65536 staticNttWords (by rw [TableConstants.staticNttWords_length]; decide)
    i (by rw [TableConstants.staticNttWords_length]; exact hi)

theorem nttSat_reduced : Reduced nttSat.mem 4096 := by
  intro i hi
  simp only [nttSat,coeffAt,Mem.readW,BitVec.setWidth_eq]
  rw [Mem.read_eq_of_bytes (v := (0#32)) ?_]
  · decide
  · intro j hj
    have ha : ¬ ((4096+BitVec.ofNat 64 (4*i)+BitVec.ofNat 64 j)-65536).toNat<8*staticNttWords.length := by
      rw [TableConstants.staticNttWords_length]
      have hi' : i<256 := hi
      simp only [BitVec.toNat_sub,BitVec.toNat_add,BitVec.toNat_ofNat,show (4096:BitVec 64).toNat=4096 by decide,
        show (65536:BitVec 64).toNat=65536 by decide]
      omega
    simp only [constMem,ha,ite_false]
    simp

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `NttVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem nttConsts_eq : nttConsts=[("VG_MLDSA_NTT_EXPANDED",staticNttWords)] := rfl

theorem positiveNtt_pre {s : State}
    (h : (positiveNttContract (abi.withConsts nttConsts)).pre s) : positiveNttK.pre s := by
  sig_pre [positiveNttContract,positiveNttSig,abi,argRegs,nttConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,TableConstants.staticNttWords_length,stackBelow] at h
  obtain ⟨hd,held,_,hsep,ht,hw,_,hred⟩ := h
  have hrd : s.rd=[expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")] := by
    rw [← List.take_append_drop (s.rd.length-1) s.rd,ht,hd]
    rfl
  refine ⟨by rw [hrd]; simp,by rw [hw]; simp [outputRegion],?_,?_,hred⟩
  · exact hsep _ (by rw [hw]; simp [outputRegion])
  · intro i hi
    have hh := held i hi
    have eq (xs : List (BitVec 64)) (j : Nat) (hj : j<xs.length) : xs.getD j 0=xs[j]! := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some,getElem!_pos xs j hj]
    exact hh.trans (eq _ _ (by rw [TableConstants.staticNttWords_length]; exact hi))

 theorem positiveNtt_spec_pre {s : State}
    (hrd : s.rd=[expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")])
    (hwr : s.wr=[outputRegion (s.gpr .x0)])
    (held : ∀ i<488,s.mem.readW (s.syms "VG_MLDSA_NTT_EXPANDED"+BitVec.ofNat 64 (8*i)) 64=
      staticNttWords.getD i 0)
    (hfit : (s.syms "VG_MLDSA_NTT_EXPANDED").toNat+3904≤2^64)
    (hsep : (expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")).Disjoint (outputRegion (s.gpr .x0)))
    (hpfit : (s.gpr .x0).toNat+1024≤2^64) (hred : Reduced s.mem (s.gpr .x0)) :
    (positiveNttContract (abi.withConsts nttConsts)).pre s := by
  sig_pre [positiveNttContract,positiveNttSig,abi,argRegs,nttConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,TableConstants.staticNttWords_length,stackBelow]
  refine ⟨by rw [hrd]; rfl,held,hfit,?_,by rw [hrd]; rfl,hwr,hpfit,hred⟩
  intro r hr
  rw [hwr] at hr
  have he := List.mem_singleton.mp hr
  subst r
  exact hsep

theorem positiveNtt_sat : (positiveNttContract (abi.withConsts nttConsts)).pre nttSat := by
  exact positiveNtt_spec_pre rfl rfl nttSat_held (by decide)
    (Region.disjoint_of_sep (by decide)) (by decide) nttSat_reduced

/-- A separate positive-output contract: no canonical-output claim is used. -/
theorem positiveNtt_verified : Verified target staticNtt
    (positiveNttContract (abi.withConsts nttConsts)) := by
  refine Verified.of_correct positiveNtt_correct positiveNtt_ct
    { pre := fun _ h => positiveNtt_pre h,post := ?_,pub := ?_,sat := ⟨nttSat,positiveNtt_sat⟩ }
  · intro s t _ h
    sig_post [positiveNttContract,positiveNttSig,abi,argRegs,Abi.withConsts,nttConsts_eq]
    exact h
  · intro s t _ _ h
    sig_pub [positiveNttContract,positiveNttSig,abi,argRegs,Abi.withConsts,nttConsts_eq] at h
    exact ⟨h.2.2,h.1,h.2.1⟩

end VG.Proof.MlDsa.AArch64.Optimized

end
