import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezeArgs
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def pairWrites (p a b : Addr) : List Region := [pairR p,rateR a,rateR b]

structure PairLayout (s : State) (p a b : Addr) : Prop where
 read : ∀i<25,InRegions (s.rd++s.wr) (wordAddr p i) 16
 stateWrite : ∀i<25,InRegions s.wr (wordAddr p i) 16
 leftWrite : ∀i<17,InRegions s.wr (outAddr a i) 8
 rightWrite : ∀i<17,InRegions s.wr (outAddr b i) 8
 outputs : (rateR a).Disjoint (rateR b)
 left : (pairR p).Disjoint (rateR a)
 right : (pairR p).Disjoint (rateR b)

theorem PairLayout.keep {s t : State} {p a b : Addr} (h : PairLayout s p a b)
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) : PairLayout t p a b := by
  rcases h with ⟨hi,hp,ha,hb,hd,hpa,hpb⟩
  exact ⟨by simpa only [hr,hw] using hi,by simpa only [hw] using hp,
    by simpa only [hw] using ha,by simpa only [hw] using hb,hd,hpa,hpb⟩

theorem blockKeep_reg {s t : State} (h : BlockKeep s t) : RegKeep [.x6,.x7,.x16] s t := by
  refine ⟨?_,h.rd,h.wr,h.sp⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  exact h.gpr r hr.1 hr.2.1 hr.2.2

structure FourPairPost (s t : State) (p q a b c d : Addr)
    (A B C D : Spec.Sha3.State) : Prop where
 keep : RegKeep [.x6,.x7,.x16] s t
 frame : Frame (pairWrites p a b++pairWrites q c d) s.mem t.mem
 first : PairAt t.mem p (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B)
 second : PairAt t.mem q (Spec.Sha3.keccakF C) (Spec.Sha3.keccakF D)
 a : Rate136 t.mem a (Spec.Sha3.keccakF A)
 b : Rate136 t.mem b (Spec.Sha3.keccakF B)
 c : Rate136 t.mem c (Spec.Sha3.keccakF C)
 d : Rate136 t.mem d (Spec.Sha3.keccakF D)

theorem pairFour_ok (sha3 : Bool) {s : State} {p q a b c d : Addr}
    {A B C D : Spec.Sha3.State}
    (hp : s.gpr .x22=p) (hq : s.gpr .x23=q) (ha : s.gpr .x24=a)
    (hb : s.gpr .x25=b) (hc : s.gpr .x26=c) (hd : s.gpr .x27=d)
    (hP : PairAt s.mem p A B) (hQ : PairAt s.mem q C D)
    (hL : PairLayout s p a b) (hR : PairLayout s q c d)
    (hsep : ∀r∈pairWrites p a b,∀t∈pairWrites q c d,r.Disjoint t) :
    WP isa (.seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.pair sha3 .x22 .x24 .x25)
      (Impl.MlDsa.AArch64.Optimized.BoundedFour.pair sha3 .x23 .x26 .x27)) s fun t=>
      FourPairPost s t p q a b c d A B C D := by
  refine WP.seq (WP.mono (pair_ok sha3 hp ha hb (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hP hL.read hL.stateWrite
    hL.leftWrite hL.rightWrite hL.outputs hL.left hL.right) fun u ⟨hu,hpu,hau,hbu,hfu⟩=>?_)
  have hqu : PairAt u.mem q C D := pairAt_keep hQ hfu (fun r hr=>
    (hsep r hr _ (by simp [pairWrites])).symm)
  have hr:=hR.keep hu.rd hu.wr
  refine WP.mono (pair_ok sha3 ((hu.gpr .x23 (by decide) (by decide) (by decide)).trans hq)
    ((hu.gpr .x26 (by decide) (by decide) (by decide)).trans hc)
    ((hu.gpr .x27 (by decide) (by decide) (by decide)).trans hd)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hqu hr.read hr.stateWrite hr.leftWrite hr.rightWrite hr.outputs hr.left hr.right)
    fun t ⟨ht,hqt,hct,hdt,hft⟩=>?_
  refine ⟨((blockKeep_reg hu).trans (blockKeep_reg ht)).mono (by decide),?_,?_,hqt,?_,?_,hct,hdt⟩
  · exact (hfu.mono (fun r hr=>List.mem_append_left _ hr)).trans
      (hft.mono (fun r hr=>List.mem_append_right _ hr))
  · exact pairAt_keep hpu hft (hsep _ (by simp [pairWrites]))
  · exact hau.keep hft (hsep _ (by simp [pairWrites]))
  · exact hbu.keep hft (hsep _ (by simp [pairWrites]))

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
