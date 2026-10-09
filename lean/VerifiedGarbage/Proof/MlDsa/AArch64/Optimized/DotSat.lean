import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotContract

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

def dotSat (count : Nat) : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 16384 else if r=.x2 then 32768 else if r=.x3 then 8192 else 0
  sp := 131072
  syms _ := 65536
  mem := constMem 65536 expandedWords
  rd := [⟨16384,1024*count⟩,⟨32768,1024*count⟩,⟨65536,3904⟩]
  wr := [⟨4096,1024⟩,⟨8192,1024⟩]

theorem dotSat_held (count : Nat) : ∀i<488,
    (dotSat count).mem.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0 := inverseSat_held

theorem dotSat_reduced (count : Nat) (p : Addr) (hp : p.toNat+1024≤65536) : Reduced (dotSat count).mem p := by
  intro i hi
  simp only [dotSat,coeffAt,Mem.readW,BitVec.setWidth_eq]
  rw [Mem.read_eq_of_bytes (v:=(0#32)) ?_]
  · decide
  · intro j hj
    have ha : ¬ ((p+BitVec.ofNat 64 (4*i)+BitVec.ofNat 64 j)-65536).toNat<8*expandedWords.length := by
      rw [InverseTable.expandedWords_length]
      have hi' : i<256 := hi
      simp only [BitVec.toNat_sub,BitVec.toNat_add,BitVec.toNat_ofNat,
        show (65536:BitVec 64).toNat=65536 by decide]
      omega
    simp only [constMem,ha,ite_false]
    simp

theorem dot_spec_pre {count : Nat} {s : State} (hc : count≤7)
    (hg0 : s.gpr .x0=4096) (hg1 : s.gpr .x1=16384) (hg2 : s.gpr .x2=32768)
    (hg3 : s.gpr .x3=8192) (hsym : s.syms "VG_MLDSA_INV_FOLDED"=65536)
    (hrd : s.rd=[⟨16384,1024*count⟩,⟨32768,1024*count⟩,⟨65536,3904⟩])
    (hwr : s.wr=[⟨4096,1024⟩,⟨8192,1024⟩])
    (held : ∀i<488,s.mem.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (ha : ∀j<count,PositiveReduced s.mem (16384+BitVec.ofNat 64 (1024*j)))
    (hb : ∀j<count,PositiveReduced s.mem (32768+BitVec.ofNat 64 (1024*j))) :
    (dotInverseContract count (abi.withConsts inverseConsts)).pre s := by
  sig_pre [dotInverseContract,dotInverseSig,abi,argRegs,inverseConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow]
  rw [hg0,hg1,hg2,hg3,hsym,hrd,hwr]
  have he : count*256*4=1024*count := by omega
  rw [he]
  refine ⟨rfl,held,by decide,?_,rfl,rfl,?_,?_,?_,?_,?_,by decide,?_,?_,by decide,ha,hb⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · exact Region.disjoint_of_sep (by simp [Region.sep]; omega)
  · exact Region.disjoint_of_sep (by simp [Region.sep]; omega)
  · exact Region.disjoint_of_sep (by decide)
  · exact Region.disjoint_of_sep (by simp [Region.sep]; omega)
  · exact Region.disjoint_of_sep (by simp [Region.sep]; omega)
  · simp; omega
  · simp; omega

theorem dot_sat (count : Nat) (hc : count≤7) :
    (dotInverseContract count (abi.withConsts inverseConsts)).pre (dotSat count) := by
  apply dot_spec_pre hc rfl rfl rfl rfl rfl rfl rfl (dotSat_held count)
  · intro j hj i hi
    have hr := dotSat_reduced count (16384+BitVec.ofNat 64 (1024*j)) (by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat, show (16384:Addr).toNat=16384 by decide]; omega) i hi
    change _<3*8380417
    change _<8380417 at hr
    omega
  · intro j hj i hi
    have hr := dotSat_reduced count (32768+BitVec.ofNat 64 (1024*j)) (by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat, show (32768:Addr).toNat=32768 by decide]; omega) i hi
    change _<3*8380417
    change _<8380417 at hr
    omega

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
