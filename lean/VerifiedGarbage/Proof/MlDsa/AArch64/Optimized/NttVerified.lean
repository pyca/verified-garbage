import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttContract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttSat
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts

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
