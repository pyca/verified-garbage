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

structure FourPairPost (s t : State) (p q a b c d w : Addr)
    (A B C D : Spec.Sha3.State) : Prop where
 keep : RegKeep blockRegs s t
 frame : Frame (pairWrites p a b++pairWrites q c d++[X2.callR w]) s.mem t.mem
 first : PairAt t.mem p (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B)
 second : PairAt t.mem q (Spec.Sha3.keccakF C) (Spec.Sha3.keccakF D)
 a : Rate136 t.mem a (Spec.Sha3.keccakF A)
 b : Rate136 t.mem b (Spec.Sha3.keccakF B)
 c : Rate136 t.mem c (Spec.Sha3.keccakF C)
 d : Rate136 t.mem d (Spec.Sha3.keccakF D)

theorem pairFour_ok (sha3 : Bool) {s : State} {p q a b c d w : Addr}
    {A B C D : Spec.Sha3.State}
    (hp : s.gpr .x22=p) (hq : s.gpr .x23=q) (ha : s.gpr .x24=a)
    (hb : s.gpr .x25=b) (hc : s.gpr .x26=c) (hd : s.gpr .x27=d)
    (hw : s.gpr .x19+BitVec.ofNat 64 Impl.MlDsa.AArch64.Optimized.BoundedFour.oX2=w)
    (hP : PairAt s.mem p A B) (hQ : PairAt s.mem q C D)
    (hL : PairLayout s p a b) (hR : PairLayout s q c d)
    (hsep : ∀r∈pairWrites p a b,∀t∈pairWrites q c d,r.Disjoint t)
    (hscr : ∀r∈pairWrites p a b++pairWrites q c d,r.Disjoint (X2.callR w))
    (hcP : Covers [pairR p,X2.callR w] s.wr) (hcQ : Covers [pairR q,X2.callR w] s.wr) :
    WP isa (.seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.pair sha3 .x22 .x24 .x25)
      (Impl.MlDsa.AArch64.Optimized.BoundedFour.pair sha3 .x23 .x26 .x27)) s fun t=>
      FourPairPost s t p q a b c d w A B C D := by
  refine WP.seq (WP.mono (pair_ok sha3 hp ha hb hw (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hP hL.read hL.leftWrite hL.rightWrite hL.outputs hL.left hL.right
    (hscr _ (by simp [pairWrites])) hcP) fun u ⟨hu,hpu,hau,hbu,hfu⟩=>?_)
  have hfu1 : ∀r∈pairWrites q c d,∀r'∈[pairR p,rateR a,rateR b,X2.callR w],r.Disjoint r' := by
    intro r hr r' hr'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr'
    rcases hr' with rfl|rfl|rfl|rfl
    · exact (hsep _ (by simp [pairWrites]) r hr).symm
    · exact (hsep _ (by simp [pairWrites]) r hr).symm
    · exact (hsep _ (by simp [pairWrites]) r hr).symm
    · exact hscr r (List.mem_append_right _ hr)
  have hqu : PairAt u.mem q C D := pairAt_keep hQ hfu (hfu1 _ (by simp [pairWrites]))
  have hr:=hR.keep hu.rd hu.wr
  refine WP.mono (pair_ok sha3 ((hu.gpr .x23 (by decide)).trans hq)
    ((hu.gpr .x26 (by decide)).trans hc) ((hu.gpr .x27 (by decide)).trans hd)
    (by rw [hu.gpr .x19 (by decide)]; exact hw)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    hqu hr.read hr.leftWrite hr.rightWrite hr.outputs hr.left hr.right
    (hscr _ (by simp [pairWrites])) (by rw [hu.wr]; exact hcQ))
    fun t ⟨ht,hqt,hct,hdt,hft⟩=>?_
  have hft1 : ∀r∈pairWrites p a b,∀r'∈[pairR q,rateR c,rateR d,X2.callR w],r.Disjoint r' := by
    intro r hr r' hr'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr'
    rcases hr' with rfl|rfl|rfl|rfl
    · exact hsep r hr _ (by simp [pairWrites])
    · exact hsep r hr _ (by simp [pairWrites])
    · exact hsep r hr _ (by simp [pairWrites])
    · exact hscr r (List.mem_append_left _ hr)
  refine ⟨(hu.trans ht).mono (by decide),?_,?_,hqt,?_,?_,hct,hdt⟩
  · exact (hfu.mono (fun r hr=>by
      simp only [pairWrites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      rcases hr with h|h|h|h <;> simp [h])).trans
      (hft.mono (fun r hr=>by
      simp only [pairWrites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      rcases hr with h|h|h|h <;> simp [h]))
  · exact pairAt_keep hpu hft (hft1 _ (by simp [pairWrites]))
  · exact hau.keep hft (hft1 _ (by simp [pairWrites]))
  · exact hbu.keep hft (hft1 _ (by simp [pairWrites]))

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
