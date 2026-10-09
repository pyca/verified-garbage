import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSatMemory
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHintPreIntro

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

def hintSatWith (m : Mem) : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 8192 else if r=.x2 then 12288
    else if r=.x3 then 16384 else if r=.x4 then 20480 else if r=.x5 then 95232
    else if r=.x6 then 95232 else 0
  sp := 131072
  syms _ := 65536
  mem := m
  rd := [⟨4096,1024⟩,⟨8192,2048⟩,⟨16384,2048⟩,⟨65536,4096⟩]
  wr := [⟨12288,2048⟩,⟨20480,2176⟩]

theorem hintSatWith_pre (m : Mem)
    (held : ∀i<512,m.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (hprod : pairedProductsReduced m 4096 8192)
    (hdata : ∀j<2,ResponseDecomposed m (pairPolyPtr 12288 j) (pairPolyPtr 16384 j) 95232) :
    (pairedHintContract (abi.withConsts pairedConsts)).pre (hintSatWith m) := by
  apply pairedHint_pre_intro (s:=hintSatWith m) ?_ held (by dsimp only [hintSatWith]; decide) (by dsimp only [hintSatWith]; decide) (by dsimp only [hintSatWith]; decide) (by dsimp only [hintSatWith]; decide) (by dsimp only [hintSatWith]; decide) (by dsimp only [hintSatWith]; decide)
  refine ⟨rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,hprod,hdata,rfl,by dsimp only [hintSatWith]; decide⟩
  · intro i hi
    refine (held i hi).trans ?_
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [PairedTable.expandedWords_length]; exact hi),
      Option.getD_some,getElem!_pos _ _ (by rw [PairedTable.expandedWords_length]; exact hi)]
  · intro r hr
    change r∈[⟨12288,2048⟩,⟨20480,2176⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact Region.disjoint_of_sep (by dsimp only [hintSatWith]; decide)
  all_goals exact Region.disjoint_of_sep (by dsimp only [hintSatWith]; decide)

def hintSat : State := hintSatWith pairedSatMem

theorem pairedHint_sat : (pairedHintContract (abi.withConsts pairedConsts)).pre hintSat := by
  apply hintSatWith_pre pairedSatMem pairedSat_held
  · refine ⟨pairedSat_positive (by decide : 4096≤32768),?_⟩
    intro j hj
    change PositiveReduced pairedSatMem (8192+BitVec.ofNat 64 (1024*j))
    rw [show (8192:BitVec 64)=BitVec.ofNat 64 8192 by rfl,←BitVec.ofNat_add]
    exact pairedSat_positive (by omega)
  · intro j hj i hi
    have hl : coeffAt pairedSatMem (pairPolyPtr 12288 j) i=0 := by
      change coeffAt pairedSatMem (12288+BitVec.ofNat 64 (1024*j)) i=0
      rw [show (12288:BitVec 64)=BitVec.ofNat 64 12288 by rfl,←BitVec.ofNat_add]
      exact pairedSat_coeff_zero (by omega) hi
    have hh : coeffAt pairedSatMem (pairPolyPtr 16384 j) i=0 := by
      change coeffAt pairedSatMem (16384+BitVec.ofNat 64 (1024*j)) i=0
      rw [show (16384:BitVec 64)=BitVec.ofNat 64 16384 by rfl,←BitVec.ofNat_add]
      exact pairedSat_coeff_zero (by omega) hi
    simp only [responseHintBase,hl,hh]
    decide

end VG.Proof.MlDsa.AArch64.Optimized.Paired
