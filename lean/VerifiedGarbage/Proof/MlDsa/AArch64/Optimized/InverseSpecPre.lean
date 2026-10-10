import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableMemory
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.InverseTable
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
import VerifiedGarbage.Spec.MlDsa.Montgomery

/-! ## From `InverseSat.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

def inverseSat : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 8192 else 0
  sp := 131072
  syms _ := 65536
  mem := constMem 65536 expandedWords
  rd := [⟨65536,3904⟩]
  wr := [⟨4096,1024⟩,⟨8192,1024⟩]

theorem inverseSat_held : ∀ i<488,
    inverseSat.mem.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0 := by
  intro i hi
  dsimp only [inverseSat]
  exact constMem_held 65536 expandedWords (by rw [InverseTable.expandedWords_length]; decide)
    i (by rw [InverseTable.expandedWords_length]; exact hi)

theorem inverseSat_reduced : Reduced inverseSat.mem 4096 := by
  intro i hi
  simp only [inverseSat,coeffAt,Mem.readW,BitVec.setWidth_eq]
  rw [Mem.read_eq_of_bytes (v := (0#32)) ?_]
  · decide
  · intro j hj
    have ha : ¬ ((4096+BitVec.ofNat 64 (4*i)+BitVec.ofNat 64 j)-65536).toNat<8*expandedWords.length := by
      rw [InverseTable.expandedWords_length]
      have hi' : i<256 := hi
      simp only [BitVec.toNat_sub,BitVec.toNat_add,BitVec.toNat_ofNat,show (4096:BitVec 64).toNat=4096 by decide,
        show (65536:BitVec 64).toNat=65536 by decide]
      omega
    simp only [constMem,ha,ite_false]
    simp

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseSpecPre.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

theorem inverseConsts_eq : inverseConsts=[("VG_MLDSA_INV_FOLDED",expandedWords)] := rfl

theorem inverse_spec_pre {s : State}
    (hrd : s.rd=[⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩])
    (hwr : s.wr=[⟨s.gpr .x0,1024⟩,⟨s.gpr .x1,1024⟩])
    (held : ∀ i<488,s.mem.readW (s.syms "VG_MLDSA_INV_FOLDED"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (hfit : (s.syms "VG_MLDSA_INV_FOLDED").toNat+3904≤2^64)
    (hsep : ∀ r∈s.wr, (⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩ : Region).Disjoint r)
    (hbuf : (⟨s.gpr .x0,1024⟩ : Region).Disjoint ⟨s.gpr .x1,1024⟩)
    (hf : (s.gpr .x0).toNat+1024≤2^64) (hs : (s.gpr .x1).toNat+1024≤2^64)
    (hred : Reduced s.mem (s.gpr .x0)) :
    (montgomeryNttInvContract (abi.withConsts inverseConsts)).pre s := by
  sig_pre [montgomeryNttInvContract,inPlaceContract,inPlaceSig,abi,argRegs,inverseConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow]
  exact ⟨by rw [hrd]; rfl,held,hfit,hsep,by rw [hrd]; rfl,hwr,hbuf,hf,hs,hred⟩

theorem inverse_sat : (montgomeryNttInvContract (abi.withConsts inverseConsts)).pre inverseSat := by
  apply inverse_spec_pre rfl rfl inverseSat_held (by decide) ?_
    (Region.disjoint_of_sep (by decide)) (by decide) (by decide) inverseSat_reduced
  intro r hr
  change r∈[⟨4096,1024⟩,⟨8192,1024⟩] at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
