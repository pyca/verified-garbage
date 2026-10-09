import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductContract

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

def productSatWith (m : Mem) : State where
  gpr r := if r=.x0 then 8192 else if r=.x1 ∨ r=.x2 then 4096 else if r=.x3 then 12288 else 0
  sp := 131072
  syms _ := 65536
  mem := m
  rd := [⟨4096,1024⟩,⟨4096,1024⟩,⟨65536,3904⟩]
  wr := [⟨8192,1024⟩,⟨12288,1024⟩]

theorem reduced_positive {m : Mem} {p : Addr} (h : Reduced m p) : PositiveReduced m p := by
  intro i hi
  exact Nat.lt_trans (h i hi) (by decide : q<3*q)

theorem inverseSat_positive : PositiveReduced inverseSat.mem (4096 : Addr) := by
  apply reduced_positive
  exact inverseSat_reduced

theorem productRaw_spec_pre {s : State}
    (hrd : s.rd=[⟨s.gpr .x1,1024⟩,⟨s.gpr .x2,1024⟩,⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩])
    (hwr : s.wr=[⟨s.gpr .x0,1024⟩,⟨s.gpr .x3,1024⟩])
    (held : ∀ i<488,s.mem.readW (s.syms "VG_MLDSA_INV_FOLDED"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (hfit : (s.syms "VG_MLDSA_INV_FOLDED").toNat+3904≤2^64)
    (hsep : ∀ r∈s.wr, (⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩ : Region).Disjoint r)
    (h01 : (⟨s.gpr .x0,1024⟩ : Region).Disjoint ⟨s.gpr .x1,1024⟩)
    (h02 : (⟨s.gpr .x0,1024⟩ : Region).Disjoint ⟨s.gpr .x2,1024⟩)
    (h03 : (⟨s.gpr .x0,1024⟩ : Region).Disjoint ⟨s.gpr .x3,1024⟩)
    (h13 : (⟨s.gpr .x1,1024⟩ : Region).Disjoint ⟨s.gpr .x3,1024⟩)
    (h23 : (⟨s.gpr .x2,1024⟩ : Region).Disjoint ⟨s.gpr .x3,1024⟩)
    (hf0 : (s.gpr .x0).toNat+1024≤2^64) (hf1 : (s.gpr .x1).toNat+1024≤2^64)
    (hf2 : (s.gpr .x2).toNat+1024≤2^64) (hf3 : (s.gpr .x3).toNat+1024≤2^64)
    (ha : PositiveReduced s.mem (s.gpr .x1)) (hb : PositiveReduced s.mem (s.gpr .x2)) :
    (multiplyInverseRawContract (abi.withConsts inverseConsts)).pre s := by
  sig_pre [multiplyInverseRawContract,multiplyInverseRawSig,multiplyInverseSig,abi,argRegs,
    inverseConsts_eq,Abi.withConsts,Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow]
  exact ⟨by rw [hrd]; rfl,held,hfit,hsep,by rw [hrd]; rfl,hwr,h01,h02,h03,h13,h23,hf0,hf1,hf2,hf3,ha,hb⟩

theorem productSatWith_pre (m : Mem)
    (held : ∀ i<488,m.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (hpos : PositiveReduced m 4096) :
    (multiplyInverseRawContract (abi.withConsts inverseConsts)).pre (productSatWith m) := by
  apply productRaw_spec_pre (s := productSatWith m) rfl rfl held (by dsimp only [productSatWith]; decide) ?_
    (Region.disjoint_of_sep (by dsimp only [productSatWith]; decide)) (Region.disjoint_of_sep (by dsimp only [productSatWith]; decide))
    (Region.disjoint_of_sep (by dsimp only [productSatWith]; decide)) (Region.disjoint_of_sep (by dsimp only [productSatWith]; decide))
    (Region.disjoint_of_sep (by dsimp only [productSatWith]; decide)) (by dsimp only [productSatWith]; decide) (by dsimp only [productSatWith]; decide) (by dsimp only [productSatWith]; decide) (by dsimp only [productSatWith]; decide)
    hpos hpos
  intro r hr
  change r∈[⟨8192,1024⟩,⟨12288,1024⟩] at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by dsimp only [productSatWith]; decide)

def productSat : State := productSatWith inverseSat.mem

theorem productRaw_sat : (multiplyInverseRawContract (abi.withConsts inverseConsts)).pre productSat :=
  productSatWith_pre inverseSat.mem inverseSat_held inverseSat_positive

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
