module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeStep
public import VerifiedGarbage.Impl.MlKem.AArch64.Paired
import VerifiedGarbage.Proof.Framework.Offset

/-! # Three native SHAKE128 blocks for each matrix stream -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3 (iterF iterF_succ)

def streamR (a : Addr) : Region := ⟨a,504⟩
def blockAt (a : Addr) (j : Nat) : Addr := a+BitVec.ofNat 64 (168*j)
def Blocks (m : Mem) (a : Addr) (k : Nat) (A : Spec.Sha3.State) : Prop :=
 ∀j<k, Rate21 m (blockAt a j) (iterF (j+1) A)

theorem block_sub (a : Addr) {j : Nat} (hj : j<3) :
    Region.Sub (rateR21 (blockAt a j)) (streamR a) :=
  Offset.sub_base a (by omega)

def squeezeWrites (p a b : Addr) : List Region := [pairR p,streamR a,streamR b,X2.callR (p+1536)]

structure SInv (initial : State) (p a b : Addr) (A B : Spec.Sha3.State) (k : Nat) (s : State) : Prop where
  keep : Keep squeezeRegs initial s
  pair : PairAt s.mem p (iterF k A) (iterF k B)
  ptr : s.gpr .x19=p
  pa : s.gpr .x20=blockAt a k
  pb : s.gpr .x21=blockAt b k
  count : (s.gpr .x22).toNat=3-k
  frame : Frame (squeezeWrites p a b) initial.mem s.mem
  oa : Blocks s.mem a k A
  ob : Blocks s.mem b k B

theorem extend_blocks {m m' : Mem} {p a b : Addr} {A : Spec.Sha3.State} {k : Nat} (hk : k<3)
    (old : Blocks m a k A) (new : Rate21 m' (blockAt a k) (iterF (k+1) A))
    (hf : Frame [pairR p,rateR21 (blockAt a k),rateR21 (blockAt b k),X2.callR (p+1536)] m m')
    (hpa : (pairR p).Disjoint (streamR a)) (hab : (streamR a).Disjoint (streamR b))
    (hwa : (X2.callR (p+1536)).Disjoint (streamR a)) : Blocks m' a (k+1) A := by
  intro j hj
  by_cases he : j=k
  · subst j; exact new
  · have hjk : j<k := by omega
    intro i hi
    have hc : (rateR21 (blockAt a j)).Contains (outAddr (blockAt a j) i) 8 :=
      Offset.contains_base _ (by omega) (by omega)
    rw [hf.readW hc (by
        intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (hpa.sub_right (block_sub a (by omega))).symm
        · exact Offset.disjoint a (Or.inl (by omega)) (by omega) (by omega)
        · exact (hab.sub_left (block_sub a (by omega))).sub_right (block_sub b hk)
        · exact (hwa.sub_right (block_sub a (by omega))).symm) (by decide)]
    exact old j hjk i hi

theorem squeeze_ok {s : State} {p a b : Addr} {A B : Spec.Sha3.State}
    (hp : s.gpr .x19=p) (ha : s.gpr .x20=a) (hb : s.gpr .x21=b) (hcount : (s.gpr .x22).toNat=3)
    (pair : PairAt s.mem p A B)
    (hin : ∀i<25,InRegions (s.rd++s.wr) (wordAddr p i) 16)
    (hwa : ∀j<3,∀i<21,InRegions s.wr (outAddr (blockAt a j) i) 8)
    (hwb : ∀j<3,∀i<21,InRegions s.wr (outAddr (blockAt b j) i) 8)
    (hab : (streamR a).Disjoint (streamR b))
    (hpa : (pairR p).Disjoint (streamR a)) (hpb : (pairR p).Disjoint (streamR b))
    (hwa' : (X2.callR (p+1536)).Disjoint (streamR a))
    (hwb' : (X2.callR (p+1536)).Disjoint (streamR b))
    (hpw : (pairR p).Disjoint (X2.callR (p+1536)))
    (hcov : Covers [pairR p,X2.callR (p+1536)] s.wr) :
    WP isa Impl.MlKem.AArch64.Paired.squeeze s (SInv s p a b A B 3) := by
  apply count_loop (by decide : 0<3) (SInv s p a b A B)
  · intro k hk t h
    refine WP.mono (squeezeStep_ok h.ptr h.pa h.pb h.pair
      (fun i hi => by rw [h.keep.rd,h.keep.wr]; exact hin i hi)
      (fun i hi => by rw [h.keep.wr]; exact hwa k hk i hi)
      (fun i hi => by rw [h.keep.wr]; exact hwb k hk i hi)
      ((hab.sub_left (block_sub a hk)).sub_right (block_sub b hk))
      (hpa.sub_right (block_sub a hk)) (hpb.sub_right (block_sub b hk)) hpw
      (by rw [h.keep.wr]; exact hcov)) fun u ⟨ku,pu,au,bu,fu,ua,ub,uc⟩ => ?_
    have count : (u.gpr .x22).toNat=3-(k+1) := by
      rw [uc,toNat_sub_n (by rw [h.count]; change 1≤3-k; omega),h.count]
      change 3-k-1=3-(k+1); omega
    refine ⟨⟨(h.keep.trans ku).mono (by simp),?_,?_,?_,?_,count,?_,?_,?_⟩,by rw [count]; omega⟩
    · simpa only [iterF_succ] using pu
    · rw [ku.gpr .x19 (by decide),h.ptr]
    · rw [ua]; change a+BitVec.ofNat 64 (168*k)+BitVec.ofNat 64 168 = _
      rw [BitVec.add_assoc,← BitVec.ofNat_add]; congr 2
    · rw [ub]; change b+BitVec.ofNat 64 (168*k)+BitVec.ofNat 64 168 = _
      rw [BitVec.add_assoc,← BitVec.ofNat_add]; congr 2
    · exact h.frame.trans (fu.sub (by
        intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨pairR p,by simp [squeezeWrites],fun _ h => h⟩
        · exact ⟨streamR a,by simp [squeezeWrites],block_sub a hk⟩
        · exact ⟨streamR b,by simp [squeezeWrites],block_sub b hk⟩
        · exact ⟨X2.callR (p+1536),by simp [squeezeWrites],fun _ h => h⟩))
    · exact extend_blocks hk h.oa (by simpa only [iterF_succ] using au) fu hpa hab hwa'
    · apply extend_blocks hk h.ob (by simpa only [iterF_succ] using bu) _ hpb hab.symm hwb'
      exact fu.mono (by
        intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
        rcases hr with h | h | h | h <;> simp [h])
  · exact ⟨⟨fun _ _ => rfl,rfl,rfl,rfl,fun _ _ => rfl⟩,pair,hp,
      by simpa [blockAt] using ha,by simpa [blockAt] using hb,hcount,Frame.refl _ _,
      fun j hj => by omega,fun j hj => by omega⟩

end VG.Proof.MlKem.AArch64.Paired
