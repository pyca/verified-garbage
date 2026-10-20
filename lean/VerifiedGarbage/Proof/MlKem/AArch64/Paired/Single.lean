module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SingleStep
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Squeeze
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Five complete SHAKE128 blocks in the singleton fallback -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3 (iterF iterF_succ)

def fullR (a : Addr) : Region := ⟨a,840⟩
def singleWrites (p a : Addr) : List Region := [pairR p,fullR a,X2.callR (p+1536)]
structure SingleInv (initial : State) (p a : Addr) (A B : Spec.Sha3.State) (k : Nat) (s : State) : Prop where
  keep : Keep singleRegs initial s
  pair : PairAt s.mem p (iterF k A) (iterF k B)
  ptr : s.gpr .x19=p
  pa : s.gpr .x20=blockAt a k
  count : (s.gpr .x22).toNat=5-k
  frame : Frame (singleWrites p a) initial.mem s.mem
  out : Blocks s.mem a k A

theorem single_block_sub (a : Addr) {j : Nat} (hj : j<5) :
    Region.Sub (rateR21 (blockAt a j)) (fullR a) := Offset.sub_base a (by omega)

theorem single_ok {s : State} {p a : Addr} {A B : Spec.Sha3.State}
    (hp : s.gpr .x19=p) (ha : s.gpr .x20=a) (hcount : (s.gpr .x22).toNat=5)
    (pair : PairAt s.mem p A B)
    (hin : ∀i<21,InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (16*i)) 8)
    (hout : ∀j<5,∀i<21,InRegions s.wr (outAddr (blockAt a j) i) 8)
    (hpa : (pairR p).Disjoint (fullR a))
    (hwa : (X2.callR (p+1536)).Disjoint (fullR a))
    (hpw : (pairR p).Disjoint (X2.callR (p+1536)))
    (hcov : Covers [pairR p,X2.callR (p+1536)] s.wr) :
    WP isa (.loop singleBody (.nonzero .x .x22)) s (SingleInv s p a A B 5) := by
  apply count_loop (by decide : 0<5) (SingleInv s p a A B)
  · intro k hk t h
    refine WP.mono (singleStep_ok h.ptr h.pa h.pair
      (fun i hi => by rw [h.keep.rd,h.keep.wr]; exact hin i hi)
      (fun i hi => by rw [h.keep.wr]; exact hout k hk i hi)
      (hpa.sub_right (single_block_sub a hk)) hpw
      (by rw [h.keep.wr]; exact hcov)) fun u ⟨ku,pu,au,fu,ua,uc⟩ => ?_
    have count : (u.gpr .x22).toNat=5-(k+1) := by
      rw [uc,toNat_sub_n (by rw [h.count]; change 1≤5-k; omega),h.count]
      change 5-k-1=5-(k+1); omega
    refine ⟨⟨(h.keep.trans ku).mono (by simp),?_,?_,?_,count,?_,?_⟩,by rw [count]; omega⟩
    · simpa only [iterF_succ] using pu
    · rw [ku.gpr .x19 (by decide),h.ptr]
    · rw [ua]; change a+BitVec.ofNat 64 (168*k)+BitVec.ofNat 64 168 = _
      rw [BitVec.add_assoc,← BitVec.ofNat_add]; congr 2
    · exact h.frame.trans (fu.sub (by
        intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨pairR p,by simp [singleWrites],fun _ h => h⟩
        · exact ⟨fullR a,by simp [singleWrites],single_block_sub a hk⟩
        · exact ⟨X2.callR (p+1536),by simp [singleWrites],fun _ h => h⟩))
    · intro j hj
      by_cases he : j=k
      · subst j; simpa only [iterF_succ] using au
      · have hjk : j<k := by omega
        intro i hi
        have hc : (rateR21 (blockAt a j)).Contains (outAddr (blockAt a j) i) 8 :=
          Offset.contains_base _ (by omega) (by omega)
        rw [fu.readW hc (by
          intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact (hpa.sub_right (single_block_sub a (by omega))).symm
          · exact Offset.disjoint a (Or.inl (by omega)) (by omega) (by omega)
          · exact (hwa.sub_right (single_block_sub a (by omega))).symm) (by decide)]
        exact h.out j hjk i hi
  · exact ⟨⟨fun _ _ => rfl,rfl,rfl,rfl,fun _ _ => rfl⟩,pair,hp,
      by simpa [blockAt] using ha,hcount,Frame.refl _ _,fun j hj => by omega⟩

end VG.Proof.MlKem.AArch64.Paired
