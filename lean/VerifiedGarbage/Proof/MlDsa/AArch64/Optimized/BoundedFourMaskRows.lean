import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskOne
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatchGeometry

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

def maskedWord (m : Mem) (b p : Addr) (i j : Nat) : BitVec 32 :=
 if m.readW (countAt b i) 64=0#64 then coeffAt m (outputAt p i) j else 0#32

structure MaskRows (σ s : State) (b p : Addr) (k : Nat) : Prop where
 keep : Keep [.x3,.x4,.x5,.x6] σ s
 frame : Frame [⟨p,4096⟩] σ.mem s.mem
 counts : ∀i<4,s.mem.readW (countAt b i) 64=σ.mem.readW (countAt b i) 64
 words : ∀i<4,∀j<256,coeffAt s.mem (outputAt p i) j=
   if i<k then maskedWord σ.mem b p i j else coeffAt σ.mem (outputAt p i) j

theorem maskRows_zero (s : State) (b p : Addr) : MaskRows s s b p 0 :=
 ⟨Keep.refl _ _,Frame.refl _ _,fun _ _=>rfl,by intro i hi j hj; simp⟩

theorem maskRows_step {σ s : State} {b p : Addr} {k : Nat} (hk : k<4)
    (hs : MaskRows σ s b p k) (hb : σ.gpr .x19=b) (hp : σ.gpr .x21=p)
    (hbound : ∀i<4,(σ.mem.readW (countAt b i) 64).toNat≤256)
    (hrc : ∀i<4,InRegions (σ.rd++σ.wr) (countAt b i) 8)
    (hr : ∀i<4,∀j<64,InRegions (σ.rd++σ.wr) (outputAt p i+BitVec.ofNat 64 (16*j)) 16)
    (hw : ∀i<4,∀j<64,InRegions σ.wr (outputAt p i+BitVec.ofNat 64 (16*j)) 16)
    (hsep : ∀i<4,∀j<4,(⟨countAt b i,8⟩ : Region).Disjoint (polyR (outputAt p j))) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne k) s fun t=>MaskRows σ t b p (k+1) := by
  refine WP.mono (maskOne_ok (s := s) (b := b) (p := outputAt p k) hk (by rw [hs.keep.get .x19]; exact hb)
    (by rw [hs.keep.get .x21,hp]; rfl)
    (by rw [hs.keep.rd,hs.keep.wr]; exact hrc k hk)
    (by rw [hs.counts k hk]; exact hbound k hk)
    (fun j hj=>by rw [hs.keep.rd,hs.keep.wr]; exact hr k hk j hj)
    (fun j hj=>by rw [hs.keep.wr]; exact hw k hk j hj)) fun t ⟨ht,_,hf,hyes,hno⟩=>?_
  refine ⟨(hs.keep.trans ht).mono (by decide),hs.frame.trans (hf.sub (fun r hr=>by
    rw [List.mem_singleton.mp hr]; exact ⟨_,by simp,outputAt_sub p hk⟩)),?_,?_⟩
  · intro i hi
    rw [hf.readW (Region.contains_self _ _) (fun r hr=>by rw [List.mem_singleton.mp hr]; exact hsep i hi k hk) (by decide)]
    exact hs.counts i hi
  · intro i hi j hj
    by_cases hik : i=k
    · subst i
      rw [ite_eq_left (by omega)]
      unfold maskedWord
      by_cases hz : σ.mem.readW (countAt b k) 64=0#64
      · rw [ite_eq_left hz,hyes (by rw [hs.counts k hk]; exact hz),hs.words k hk j hj,ite_eq_right (by omega)]
      · rw [ite_eq_right hz]
        exact hno (by rw [hs.counts k hk]; exact hz) j hj
    · have hframe : coeffAt t.mem (outputAt p i) j=coeffAt s.mem (outputAt p i) j := by
        unfold coeffAt
        apply hf.readW
          (Offset.contains_base (outputAt p i) (by omega : 4*j+4≤1024) (by omega))
          (fun r hr=>by rw [List.mem_singleton.mp hr]; exact outputs_apart p hi hk hik) (by decide)
      rw [hframe,hs.words i hi j hj]
      by_cases hlt : i<k
      · rw [ite_eq_left hlt,ite_eq_left (by omega)]
      · rw [ite_eq_right hlt,ite_eq_right (by omega)]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
