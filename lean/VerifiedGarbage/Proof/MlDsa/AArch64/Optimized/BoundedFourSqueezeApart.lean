module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezeArgs

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
/-! ## From `BoundedFourSqueezeState.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/BoundedFourSqueezeStep.lean`, which only this module imported.
section

/-! ## From `BoundedFourPairFour.lean` -/

@[expose] public section

section

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

end

/-! ## From `BoundedFourSqueezeStep.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def squeezeRegs : List Reg := [.x0,.x1,.x16,.x17,.x6,.x7,.x24,.x25,.x26,.x27,.x28]

structure SqueezeStepPost (s t : State) (p q a b c d w : Addr)
    (A B C D : Spec.Sha3.State) : Prop where
 keep : RegKeep squeezeRegs s t
 frame : Frame (pairWrites p a b++pairWrites q c d++[X2.callR w]) s.mem t.mem
 first : PairAt t.mem p (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B)
 second : PairAt t.mem q (Spec.Sha3.keccakF C) (Spec.Sha3.keccakF D)
 rateA : Rate136 t.mem a (Spec.Sha3.keccakF A)
 rateB : Rate136 t.mem b (Spec.Sha3.keccakF B)
 rateC : Rate136 t.mem c (Spec.Sha3.keccakF C)
 rateD : Rate136 t.mem d (Spec.Sha3.keccakF D)
 nextA : t.gpr .x24=a+136
 nextB : t.gpr .x25=b+136
 nextC : t.gpr .x26=c+136
 nextD : t.gpr .x27=d+136
 count : t.gpr .x28=s.gpr .x28-1

theorem squeezeStep_ok (sha3 : Bool) {s : State} {p q a b c d w : Addr}
    {A B C D : Spec.Sha3.State}
    (hp : s.gpr .x22=p) (hq : s.gpr .x23=q) (ha : s.gpr .x24=a)
    (hb : s.gpr .x25=b) (hc : s.gpr .x26=c) (hd : s.gpr .x27=d)
    (hP : PairAt s.mem p A B) (hQ : PairAt s.mem q C D)
    (hL : PairLayout s p a b) (hR : PairLayout s q c d)
    (hw : s.gpr .x19+BitVec.ofNat 64 Impl.MlDsa.AArch64.Optimized.BoundedFour.oX2=w)
    (hsep : ∀r∈pairWrites p a b,∀t∈pairWrites q c d,r.Disjoint t)
    (hscr : ∀r∈pairWrites p a b++pairWrites q c d,r.Disjoint (X2.callR w))
    (hcP : Covers [pairR p,X2.callR w] s.wr) (hcQ : Covers [pairR q,X2.callR w] s.wr) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeStep sha3) s fun t=>
      SqueezeStepPost s t p q a b c d w A B C D := by
  have hh := pairFour_ok sha3 hp hq ha hb hc hd hw hP hQ hL hR hsep hscr hcP hcQ
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeStep
  rw [WP.seq_iff (M := isa)] at hh
  refine WP.seq (WP.mono hh fun u hu=>WP.seq (WP.mono hu fun v hv=>?_))
  refine WP.mono (squeezeAdvance_ok v) fun t ⟨⟨⟨h24,h25,h26,h27,h28,hm⟩,hk⟩,_⟩=>?_
  have hreg : RegKeep [.x24,.x25,.x26,.x27,.x28] v t := ⟨hk.gpr,hk.rd,hk.wr,hk.sp⟩
  refine ⟨(hv.keep.trans hreg).mono (by decide),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hm]; exact hv.frame
  · rw [hm]; exact hv.first
  · rw [hm]; exact hv.second
  · rw [hm]; exact hv.a
  · rw [hm]; exact hv.b
  · rw [hm]; exact hv.c
  · rw [hm]; exact hv.d
  · rw [h24,hv.keep.gpr .x24 (by decide),ha]
  · rw [h25,hv.keep.gpr .x25 (by decide),hb]
  · rw [h26,hv.keep.gpr .x26 (by decide),hc]
  · rw [h27,hv.keep.gpr .x27 (by decide),hd]
  · rw [h28,hv.keep.gpr .x28 (by decide)]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

structure SqueezeCfg where
 p : Addr
 q : Addr
 a : Addr
 b : Addr
 c : Addr
 d : Addr
 /-- `vg_keccak_f1600_x2`'s working space, and the return address. -/
 w : Addr

def SqueezeCfg.out (c : SqueezeCfg) (i : Nat) : Addr :=
 if i=0 then c.a else if i=1 then c.b else if i=2 then c.c else c.d

def SqueezeCfg.at (c : SqueezeCfg) (i j : Nat) : Addr := c.out i+BitVec.ofNat 64 (136*j)
def SqueezeCfg.writes (c : SqueezeCfg) : List Region :=
 [pairR c.p,pairR c.q,⟨c.a,272⟩,⟨c.b,272⟩,⟨c.c,272⟩,⟨c.d,272⟩,X2.callR c.w]
def SqueezeCfg.stepWrites (c : SqueezeCfg) (j : Nat) : List Region :=
 pairWrites c.p (c.at 0 j) (c.at 1 j)++pairWrites c.q (c.at 2 j) (c.at 3 j)++[X2.callR c.w]

structure SqueezeLayout (σ : State) (c : SqueezeCfg) : Prop where
 left : ∀j<2,PairLayout σ c.p (c.at 0 j) (c.at 1 j)
 right : ∀j<2,PairLayout σ c.q (c.at 2 j) (c.at 3 j)
 apart : ∀j<2,∀r∈pairWrites c.p (c.at 0 j) (c.at 1 j),
   ∀t∈pairWrites c.q (c.at 2 j) (c.at 3 j),r.Disjoint t
 past : ∀i<4,∀k j,k<j→j<2→∀r∈c.stepWrites j,(rateR (c.at i k)).Disjoint r
 covers : ∀j<2,∀r∈c.stepWrites j,∃t∈c.writes,Region.Sub r t
 base : σ.gpr .x19+BitVec.ofNat 64 Impl.MlDsa.AArch64.Optimized.BoundedFour.oX2=c.w
 scratch : ∀j<2,∀r∈pairWrites c.p (c.at 0 j) (c.at 1 j)++pairWrites c.q (c.at 2 j) (c.at 3 j),
   r.Disjoint (X2.callR c.w)
 callP : Covers [pairR c.p,X2.callR c.w] σ.wr
 callQ : Covers [pairR c.q,X2.callR c.w] σ.wr

structure SqueezeInv (σ s : State) (c : SqueezeCfg) (A : Nat→Spec.Sha3.State) (j : Nat) : Prop where
 bound : j≤2
 keep : RegKeep squeezeRegs σ s
 frame : Frame c.writes σ.mem s.mem
 first : PairAt s.mem c.p (Resident.permuted (A 0) j) (Resident.permuted (A 1) j)
 second : PairAt s.mem c.q (Resident.permuted (A 2) j) (Resident.permuted (A 3) j)
 streams : ∀i<4,Stream136 s.mem (c.out i) j (A i)
 r22 : s.gpr .x22=c.p
 r23 : s.gpr .x23=c.q
 r24 : s.gpr .x24=c.at 0 j
 r25 : s.gpr .x25=c.at 1 j
 r26 : s.gpr .x26=c.at 2 j
 r27 : s.gpr .x27=c.at 3 j
 count : s.gpr .x28=BitVec.ofNat 64 (2-j)

theorem SqueezeCfg.next (c : SqueezeCfg) (i j : Nat) : c.at i j+136=c.at i (j+1) := by
  simp only [SqueezeCfg.at,BitVec.add_assoc]
  change c.out i+(BitVec.ofNat 64 (136*j)+BitVec.ofNat 64 136)=_
  rw [←BitVec.ofNat_add,show 136*j+136=136*(j+1) by omega_arith]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourSqueezeLoopStep.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem squeezeLoopStep_ok (sha3 : Bool) {σ s : State} {c : SqueezeCfg}
    {A : Nat→Spec.Sha3.State} {j : Nat} (hl : SqueezeLayout σ c)
    (hi : SqueezeInv σ s c A j) (hj : j<2) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeStep sha3) s fun t=>
      SqueezeInv σ t c A (j+1) := by
  refine WP.mono (squeezeStep_ok sha3 hi.r22 hi.r23 hi.r24 hi.r25 hi.r26 hi.r27
    hi.first hi.second ((hl.left j hj).keep hi.keep.rd hi.keep.wr)
    ((hl.right j hj).keep hi.keep.rd hi.keep.wr)
    (by rw [hi.keep.gpr .x19 (by decide)]; exact hl.base) (hl.apart j hj) (hl.scratch j hj)
    (by rw [hi.keep.wr]; exact hl.callP) (by rw [hi.keep.wr]; exact hl.callQ)) fun t ht=>?_
  have hf : Frame (c.stepWrites j) s.mem t.mem := ht.frame
  refine ⟨by omega_arith,(hi.keep.trans ht.keep).mono (by decide),hi.frame.trans (hf.sub (hl.covers j hj)),
    ht.first,ht.second,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi4
    refine ((hi.streams i hi4).keep hf (fun k hk=>hl.past i hi4 k j hk hj)).succ ?_
    rcases (show i=0∨i=1∨i=2∨i=3 by omega_arith) with rfl|rfl|rfl|rfl
    · exact ht.rateA
    · exact ht.rateB
    · exact ht.rateC
    · exact ht.rateD
  · rw [ht.keep.gpr .x22 (by decide)]; exact hi.r22
  · rw [ht.keep.gpr .x23 (by decide)]; exact hi.r23
  · rw [ht.nextA,c.next]
  · rw [ht.nextB,c.next]
  · rw [ht.nextC,c.next]
  · rw [ht.nextD,c.next]
  · rw [ht.count,hi.count]
    change BitVec.ofNat 64 (2-j)-1#64=_
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (2-j) 1 (by decide) (by omega_arith)]
    congr 1

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourSqueezeLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

theorem squeezeGuard {σ s : State} {c : SqueezeCfg} {A : Nat→Spec.Sha3.State} {j : Nat}
    (hi : SqueezeInv σ s c A j) :
    isa.eval (.nonzero .x .x28) s=some (decide (j<2)) := by
  rw [eval_nonzero,hi.count,ne_zero_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_arith)]
  congr 1
  apply decide_eq_decide.mpr
  have:=hi.bound
  omega_arith

theorem squeezeLoop_ok (sha3 : Bool) {σ s : State} {c : SqueezeCfg}
    {A : Nat→Spec.Sha3.State} {j : Nat} (hl : SqueezeLayout σ c)
    (hi : SqueezeInv σ s c A j) (hj : j<2) :
    WP isa (.loop (Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeStep sha3) (.nonzero .x .x28)) s
      (fun t=>SqueezeInv σ t c A 2) := by
  refine WP.loop (M := isa) (fun rank s=>∃j,rank=2-j ∧ SqueezeInv σ s c A j ∧j<2)
    ?_ (2-j) s ⟨j,rfl,hi,hj⟩
  rintro rank s ⟨j,rfl,hi,hj⟩
  refine WP.mono (squeezeLoopStep_ok sha3 hl hi hj) fun t ht=>?_
  have hg:=squeezeGuard ht
  by_cases hn : j+1<2
  · exact .inr ⟨by rw [hg,decide_eq_true hn],2-(j+1),by omega_arith,j+1,rfl,ht,hn⟩
  · have he : j+1=2 := by omega_arith
    exact .inl ⟨by rw [hg,decide_eq_false hn],by rw [←he]; exact ht⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourSqueezeLayout.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def squeezeCfg (b : Addr) (off : Nat) : SqueezeCfg :=
 ⟨b,b+400#64,b+BitVec.ofNat 64 (840+off),b+BitVec.ofNat 64 (1384+off),
  b+BitVec.ofNat 64 (1928+off),b+BitVec.ofNat 64 (2472+off),
  b+BitVec.ofNat 64 Impl.MlDsa.AArch64.Optimized.BoundedFour.oX2⟩

theorem squeezeCfg_out (b : Addr) (off : Nat) {i : Nat} (hi : i<4) :
    (squeezeCfg b off).out i=b+BitVec.ofNat 64 (840+544*i+off) := by
  rcases (show i=0∨i=1∨i=2∨i=3 by omega_arith) with rfl|rfl|rfl|rfl <;> rfl

theorem squeezeCfg_at (b : Addr) (off : Nat) {i : Nat} (hi : i<4) (j : Nat) :
    (squeezeCfg b off).at i j=b+BitVec.ofNat 64 (840+544*i+off+136*j) := by
  rw [SqueezeCfg.at,squeezeCfg_out b off hi,BitVec.add_assoc,←BitVec.ofNat_add]

theorem pairLayout_offsets {s : State} {b : Addr} {d a e : Nat}
    (hd : d+400≤8192) (ha : a+136≤e) (he : e+136≤8192) (hda : d+400≤a)
    (hw : ∀o n,o+n≤8192→InRegions s.wr (b+BitVec.ofNat 64 o) n) :
    PairLayout s (b+BitVec.ofNat 64 d) (b+BitVec.ofNat 64 a) (b+BitVec.ofNat 64 e) := by
  constructor
  · intro i hi
    obtain ⟨r,hr,hh⟩:=hw (d+16*i) 16 (by omega_arith)
    refine ⟨r,List.mem_append_right _ hr,?_⟩
    simpa only [wordAddr,Offset.add_add] using hh
  · intro i hi
    simpa only [wordAddr,Offset.add_add] using hw (d+16*i) 16 (by omega_arith)
  · intro i hi
    simpa only [outAddr,Offset.add_add] using hw (a+8*i) 8 (by omega_arith)
  · intro i hi
    simpa only [outAddr,Offset.add_add] using hw (e+8*i) 8 (by omega_arith)
  · exact Offset.disjoint b (Or.inl ha) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint b (Or.inl hda) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint b (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)

theorem squeezeLayout_left {s : State} {b : Addr} {off j : Nat} (ho : off≤272) (hj : j<2)
    (hw : ∀o n,o+n≤8192→InRegions s.wr (b+BitVec.ofNat 64 o) n) :
    PairLayout s (squeezeCfg b off).p ((squeezeCfg b off).at 0 j) ((squeezeCfg b off).at 1 j) := by
  rw [squeezeCfg_at _ _ (by decide),squeezeCfg_at _ _ (by decide)]
  have hp : (squeezeCfg b off).p=b+BitVec.ofNat 64 0 := by simp [squeezeCfg]
  rw [hp]
  exact pairLayout_offsets (by decide) (by omega_arith) (by omega_arith) (by omega_arith) hw

theorem squeezeLayout_right {s : State} {b : Addr} {off j : Nat} (ho : off≤272) (hj : j<2)
    (hw : ∀o n,o+n≤8192→InRegions s.wr (b+BitVec.ofNat 64 o) n) :
    PairLayout s (squeezeCfg b off).q ((squeezeCfg b off).at 2 j) ((squeezeCfg b off).at 3 j) := by
  rw [squeezeCfg_at _ _ (by decide),squeezeCfg_at _ _ (by decide)]
  change PairLayout s (b+BitVec.ofNat 64 400) _ _
  exact pairLayout_offsets (by decide) (by omega_arith) (by omega_arith) (by omega_arith) hw

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourSqueezeApart.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem squeezeLayout_apart (b : Addr) {off j : Nat} (ho : off≤272) (hj : j<2) :
    ∀r∈pairWrites (squeezeCfg b off).p ((squeezeCfg b off).at 0 j) ((squeezeCfg b off).at 1 j),
    ∀t∈pairWrites (squeezeCfg b off).q ((squeezeCfg b off).at 2 j) ((squeezeCfg b off).at 3 j),r.Disjoint t := by
  intro r hr t ht
  simp only [pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr ht
  rcases hr with rfl|rfl|rfl <;> rcases ht with rfl|rfl|rfl
  · have h := Offset.disjoint b (d := 0) (n := 400) (e := 400) (k := 400)
      (by omega_arith) (by omega_arith) (by omega_arith)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 0) (n := 400) (e := 1928+off+136*j) (k := 136)
      (by omega_arith) (by omega_arith) (by omega_arith)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 0) (n := 400) (e := 2472+off+136*j) (k := 136)
      (by omega_arith) (by omega_arith) (by omega_arith)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 840+off+136*j) (n := 136) (e := 400) (k := 400)
      (by omega_arith) (by omega_arith) (by omega_arith)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 840+off+136*j) (n := 136) (e := 1928+off+136*j) (k := 136)
      (by omega_arith) (by omega_arith) (by omega_arith)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 840+off+136*j) (n := 136) (e := 2472+off+136*j) (k := 136)
      (by omega_arith) (by omega_arith) (by omega_arith)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 1384+off+136*j) (n := 136) (e := 400) (k := 400)
      (by omega_arith) (by omega_arith) (by omega_arith)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 1384+off+136*j) (n := 136) (e := 1928+off+136*j) (k := 136)
      (by omega_arith) (by omega_arith) (by omega_arith)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 1384+off+136*j) (n := 136) (e := 2472+off+136*j) (k := 136)
      (by omega_arith) (by omega_arith) (by omega_arith)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
