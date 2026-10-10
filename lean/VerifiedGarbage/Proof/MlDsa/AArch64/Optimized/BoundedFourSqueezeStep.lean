import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourPairFour

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
