import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskTiming
import VerifiedGarbage.Spec.MlDsa.ResidentMask
import VerifiedGarbage.Proof.Framework.Contract

/-! ## From `ResidentMaskContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64 VG.Spec.MlDsa

def pairK : Contract isa where
  pre := Pre
  post s t :=
    let g := (s.gpr .x1).setWidth 32 |>.toNat
    let d := 1+bitlen (g-1)
    PolyIs t.mem (s.gpr .x2) (toRq (bitUnpack (H (Spec.Sha3.bytesAt s.mem (s.gpr .x0) 66) (32*d)) (g-1) g)) ∧
    PolyIs t.mem (s.gpr .x3) (toRq (bitUnpack (H (Spec.Sha3.bytesAt s.mem (s.gpr .x0+66) 66) (32*d)) (g-1) g))
  pub := publicInputs

theorem pair_correct (core : Resident.Core) (s : State) (hp : pairK.pre s) :
    ∃ trace t, Exec isa (Impl.MlDsa.AArch64.Optimized.ResidentMask.rawWith core.code) s trace t ∧
      abiPreserved s t ∧ pairK.post s t := by
  rcases hp.gamma with hg | hg
  · obtain ⟨tr,t,he,ht⟩ := rawWith_ok core s hp (.inl rfl) hg
    refine ⟨tr,t,he,ht.1,?_⟩
    simpa only [pairK,hg,maskPoly,show (131072#32).toNat=2^17 from rfl,
      show 1+bitlen (2^17-1)=18 from rfl] using And.intro ht.2.2.1 ht.2.2.2.1
  · obtain ⟨tr,t,he,ht⟩ := rawWith_ok core s hp (.inr rfl) hg
    refine ⟨tr,t,he,ht.1,?_⟩
    simpa only [pairK,hg,maskPoly,show (524288#32).toNat=2^19 from rfl,
      show 1+bitlen (2^19-1)=20 from rfl] using And.intro ht.2.2.1 ht.2.2.2.1

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentMaskVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64 VG.Spec.MlDsa

def pairSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 131072 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000,132⟩]
  wr := [⟨0x2000,1024⟩,⟨0x3000,1024⟩,⟨0x4000,8192⟩]

theorem pair_implies : pairK.Implies (expandMaskPairContract AArch64.abi) := by
  refine { pre := ?_,post := ?_,pub := ?_,sat := ?_ }
  · intro s h
    sig_pre [expandMaskPairContract,expandMaskPairSig,AArch64.abi,AArch64.argRegs] at h
    sig_split h
    rename_i hrd hwr h02 h03 h04 h23 h24 h34 hn0 hn2 hn3 hn4
    refine ⟨by rw [hwr]; simp,by rw [hwr]; simp,by rw [hwr]; simp,
      by rw [hrd]; simp,?_,h24,h34,h23,?_⟩
    · intro r hr
      simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl <;> with_reducible assumption
    · rcases h with h | h
      · left; exact BitVec.eq_of_toNat_eq h
      · right; exact BitVec.eq_of_toNat_eq h
  · sig_implies_post [expandMaskPairContract,expandMaskPairSig,pairK,AArch64.abi,AArch64.argRegs]
  · intro s t _ _ h
    sig_pub [expandMaskPairContract,expandMaskPairSig,AArch64.abi,AArch64.argRegs] at h
    change publicInputs s t
    sig_split h
    refine ⟨⟨by assumption,?_⟩,by assumption⟩
    intro r hr
    simp only [publicRegs,Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine ⟨pairSat,?_⟩
    sig_pre [expandMaskPairContract,expandMaskPairSig,AArch64.abi,AArch64.argRegs] <;> sig_and_intros
    all_goals first | rfl | exact Region.disjoint_of_sep (by decide) | decide

theorem pair_verified : Verified AArch64.target
    Impl.MlDsa.AArch64.Optimized.ResidentMask.raw (expandMaskPairContract AArch64.abi) :=
  Verified.of_correct (pair_correct Resident.originalCore) raw_ct pair_implies

theorem pair_n2_verified : Verified AArch64.target
    (Impl.MlDsa.AArch64.Optimized.ResidentMask.rawWith Resident.n2Core.code)
    (expandMaskPairContract AArch64.abi) :=
  Verified.of_correct (pair_correct Resident.n2Core) raw_n2_ct pair_implies

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end
