import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttVerified

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem positiveNttOut_pre {s : State}
    (h : (positiveNttOutContract (abi.withConsts nttConsts)).pre s) : positiveNttOutK.pre s := by
  sig_pre [positiveNttOutContract,positiveNttOutSig,abi,argRegs,nttConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,TableConstants.staticNttWords_length,stackBelow] at h
  obtain ⟨hd,held,_,hsep,ht,hw,hio,_,_,hred⟩ := h
  have hrd : s.rd=[outputRegion (s.gpr .x1),expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")] := by
    rw [← List.take_append_drop (s.rd.length-1) s.rd,ht,hd]
    rfl
  refine ⟨by rw [hrd]; simp,by rw [hw]; simp [outputRegion],by rw [hrd]; simp,
    hio.symm,?_,?_,hred⟩
  · exact hsep _ (by rw [hw]; simp [outputRegion])
  · intro i hi
    have eq (xs : List (BitVec 64)) (j : Nat) (hj : j<xs.length) : xs.getD j 0=xs[j]! := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some,getElem!_pos xs j hj]
    exact (held i hi).trans (eq _ _ (by rw [TableConstants.staticNttWords_length]; exact hi))

theorem positiveNttOut_spec_pre {s : State}
    (hrd : s.rd=[outputRegion (s.gpr .x1),expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")])
    (hwr : s.wr=[outputRegion (s.gpr .x0)])
    (held : ∀ i<488,s.mem.readW (s.syms "VG_MLDSA_NTT_EXPANDED"+BitVec.ofNat 64 (8*i)) 64=
      staticNttWords.getD i 0)
    (hfit : (s.syms "VG_MLDSA_NTT_EXPANDED").toNat+3904≤2^64)
    (hsep : (expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")).Disjoint (outputRegion (s.gpr .x0)))
    (hio : (outputRegion (s.gpr .x0)).Disjoint (outputRegion (s.gpr .x1)))
    (hpfit : (s.gpr .x0).toNat+1024≤2^64) (hsfit : (s.gpr .x1).toNat+1024≤2^64)
    (hred : Reduced s.mem (s.gpr .x1)) :
    (positiveNttOutContract (abi.withConsts nttConsts)).pre s := by
  sig_pre [positiveNttOutContract,positiveNttOutSig,abi,argRegs,nttConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,TableConstants.staticNttWords_length,stackBelow]
  refine ⟨by rw [hrd]; rfl,held,hfit,?_,by rw [hrd]; rfl,hwr,hio,hpfit,hsfit,hred⟩
  intro r hr
  rw [hwr] at hr
  have he := List.mem_singleton.mp hr
  subst r
  exact hsep

def nttOutSat : State := { nttSat with
  gpr := fun r => if r=.x0 then 8192 else if r=.x1 then 4096 else 0
  rd := [⟨4096,1024⟩,⟨65536,3904⟩]
  wr := [⟨8192,1024⟩] }

theorem positiveNttOut_sat : (positiveNttOutContract (abi.withConsts nttConsts)).pre nttOutSat := by
  apply positiveNttOut_spec_pre (s:=nttOutSat) rfl rfl
  · simpa only [nttOutSat,show nttSat.syms "VG_MLDSA_NTT_EXPANDED"=65536 from rfl] using nttSat_held
  · decide
  · exact Region.disjoint_of_sep (by decide)
  · exact Region.disjoint_of_sep (by decide)
  · decide
  · decide
  · simpa only [nttOutSat,nttSat,show (Reg.x1=Reg.x0)=False from propext (by decide),ite_false,ite_true] using nttSat_reduced

theorem positiveNttOut_verified : Verified target outNtt
    (positiveNttOutContract (abi.withConsts nttConsts)) := by
  refine Verified.of_correct positiveNttOut_correct positiveNttOut_ct
    { pre := fun _ h => positiveNttOut_pre h,post := ?_,pub := ?_,sat := ⟨nttOutSat,positiveNttOut_sat⟩ }
  · intro s t _ h
    sig_post [positiveNttOutContract,positiveNttOutSig,abi,argRegs,Abi.withConsts,nttConsts_eq]
    exact h
  · intro s t _ _ h
    sig_pub [positiveNttOutContract,positiveNttOutSig,abi,argRegs,Abi.withConsts,nttConsts_eq] at h
    exact ⟨h.2.2.1,h.2.2.2,h.1,h.2.1⟩

end VG.Proof.MlDsa.AArch64.Optimized
