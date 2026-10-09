import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSatMemory
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZPreIntro

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

def zSatWith (m : Mem) : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 8192 else if r=.x2 then 12288
    else if r=.x3 then 16384 else if r=.x4 then 20480 else if r=.x5 then 95232
    else if r=.x6 then 1 else 0
  sp := 131072
  syms _ := 65536
  mem := m
  rd := [⟨4096,1024⟩,⟨8192,2048⟩,⟨65536,4096⟩]
  wr := [⟨12288,2048⟩,⟨20480,2176⟩]

theorem zSatWith_pre (m : Mem)
    (held : ∀i<512,m.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (hprod : pairedProductsReduced m 4096 8192)
    (hdata : ∀j<2,Reduced m (pairPolyPtr 12288 j)) :
    (pairedZContract (abi.withConsts pairedConsts)).pre (zSatWith m) := by
  apply pairedZ_pre_intro (s:=zSatWith m) ?_ held (by dsimp only [zSatWith]; decide) (by dsimp only [zSatWith]; decide) (by dsimp only [zSatWith]; decide) (by dsimp only [zSatWith]; decide) (by dsimp only [zSatWith]; decide)
  refine ⟨rfl,rfl,?_,?_,?_,?_,?_,?_,?_,hprod,hdata,by dsimp only [zSatWith]; decide,by dsimp only [zSatWith]; decide⟩
  · intro i hi
    refine (held i hi).trans ?_
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [PairedTable.expandedWords_length]; exact hi),
      Option.getD_some,getElem!_pos _ _ (by rw [PairedTable.expandedWords_length]; exact hi)]
  · intro r hr
    change r∈[⟨12288,2048⟩,⟨20480,2176⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact Region.disjoint_of_sep (by dsimp only [zSatWith]; decide)
  all_goals exact Region.disjoint_of_sep (by dsimp only [zSatWith]; decide)

def zSat : State := zSatWith pairedSatMem

theorem pairedZ_sat : (pairedZContract (abi.withConsts pairedConsts)).pre zSat := by
  apply zSatWith_pre pairedSatMem pairedSat_held
  · refine ⟨pairedSat_positive (by decide : 4096≤32768),?_⟩
    intro j hj
    change PositiveReduced pairedSatMem (8192+BitVec.ofNat 64 (1024*j))
    rw [show (8192:BitVec 64)=BitVec.ofNat 64 8192 by rfl,←BitVec.ofNat_add]
    exact pairedSat_positive (by omega)
  · intro j hj
    change Reduced pairedSatMem (12288+BitVec.ofNat 64 (1024*j))
    rw [show (12288:BitVec 64)=BitVec.ofNat 64 12288 by rfl,←BitVec.ofNat_add]
    exact pairedSat_reduced (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
