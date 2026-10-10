import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedCommitment
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Blocks
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWritten
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedMasks

/-! ## From `CachedCopyBody.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep wp_ldrx wp_strx wp_addImm wp_subImm wp_nil)

theorem copyBody_ok (s : State)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x1) 8) (hout : InRegions s.wr (s.gpr .x0) 8) :
    WP isa (.block Impl.MlDsa.AArch64.Sign.Cached.copyBody) s fun t=>
      t.mem=s.mem.writeW (s.gpr .x0) (s.mem.readW (s.gpr .x1) 64) ∧
      t.gpr .x0=s.gpr .x0+8 ∧ t.gpr .x1=s.gpr .x1+8 ∧
      t.gpr .x2=s.gpr .x2-BitVec.ofNat 64 1 ∧ Keep [.x0,.x1,.x2,.x9] s t := by
  have e0 : s.gpr .x0+BitVec.ofNat 64 0=s.gpr .x0 := BitVec.add_zero _
  have e1 : s.gpr .x1+BitVec.ofNat 64 0=s.gpr .x1 := BitVec.add_zero _
  refine wp_ldrx (a:=s.gpr .x1) (by decide) e1 hin fun a ha va=>
    wp_strx (a:=s.gpr .x0) (by decide) (by rw [ha.get .x0,e0]) (by rw [ha.wr];exact hout) fun b hb=>
    wp_addImm (by decide) fun c hc vc=>wp_addImm (by decide) fun d hd vd=>
    wp_subImm (by decide) fun t ht vt=>wp_nil ?_
  refine ⟨?_,?_,?_,?_,((((ha.keep.trans hb.keep).trans hc.keep).trans hd.keep).trans ht.keep).mono (by simp)⟩
  · rw [ht.mem,hd.mem,hc.mem,hb.mem,va,ha.mem]
  · rw [ht.get .x0,hd.get .x0,vc,show b.gpr .x0=a.gpr .x0 by rw [hb.gpr],ha.get .x0]
    rfl
  · rw [ht.get .x1,vd,hc.get .x1,show b.gpr .x1=a.gpr .x1 by rw [hb.gpr],ha.get .x1]
    rfl
  · rw [vt,hd.get .x2,hc.get .x2,show b.gpr .x2=a.gpr .x2 by rw [hb.gpr],ha.get .x2]

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedCopy.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (Keep count_loop ptr_add)
open VG.Proof.MlDsa.Pack (Written)
open VG.Proof.MlDsa.AArch64.Optimized.KeygenPack (written_word)

theorem copyMask_ok (p : Params) (s : State)
    (hin : InRegions (s.rd++s.wr) (pa s t4P) 1024)
    (hout : InRegions s.wr (pa s (yP p (p.ℓ-1))) 1024)
    (hsep : (⟨pa s t4P,1024⟩:Region).Disjoint ⟨pa s (yP p (p.ℓ-1)),1024⟩) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.copyMask p) s fun t=>
      bytesAt t.mem (pa s (yP p (p.ℓ-1))) 1024=bytesAt s.mem (pa s t4P) 1024 ∧
      Frame [⟨pa s (yP p (p.ℓ-1)),1024⟩] s.mem t.mem ∧ Keep [.x0,.x1,.x2,.x9] s t := by
  let dst := pa s (yP p (p.ℓ-1))
  let src := pa s t4P
  unfold Impl.MlDsa.AArch64.Sign.Cached.copyMask
  refine WP.seq (WP.mono (copyGlue_ok (dst:=yP p (p.ℓ-1)) (src:=t4P) (n:=128) (by change Reg.x28∈keptRegs;decide) (by decide) s)
    fun a ⟨⟨h0,h1,h2⟩,ka⟩=>?_)
  refine WP.mono (count_loop (cr:=.x2) (n:=128) (by decide) (fun k u=>
    u.gpr .x0=dst+BitVec.ofNat 64 (8*k) ∧ u.gpr .x1=src+BitVec.ofNat 64 (8*k) ∧
    u.gpr .x2=BitVec.ofNat 64 (128-k) ∧ Keep [.x0,.x1,.x2,.x9] s u ∧
    Frame [⟨dst,1024⟩] s.mem u.mem ∧
    (∀j<8*k,u.mem (dst+BitVec.ofNat 64 j)=s.mem (src+BitVec.ofNat 64 j)))
    (fun k hk u ⟨e0,e1,e2,ku,hf,hb⟩=>?_) ?_) fun t ⟨_,_,_,kt,hf,hb⟩=>?_
  · refine WP.mono (copyBody_ok u ?_ ?_) fun t ⟨hm,t0,t1,t2,kt⟩=>?_
    · rw [ku.rd,ku.wr,e1]
      exact inRegions_sub hin (by omega) (by omega)
    · rw [ku.wr,e0]
      exact inRegions_sub hout (by omega) (by omega)
    · have hw : Written u.mem t.mem (dst+BitVec.ofNat 64 (8*k)) 8
          (fun j=>s.mem (src+BitVec.ofNat 64 (8*k+j))) := by
        rw [hm,e0]
        refine (written_word u.mem _ 8 (u.mem.readW (u.gpr .x1) 64)).congr fun j hj=>?_
        rw [e1]
        simp only [Mem.readW,BitVec.setWidth_eq]
        rw [Mem.extractLsb'_read _ _ hj,ptr_add]
        exact hf.bytes (R:=⟨src,1024⟩) (by simpa only [List.mem_singleton,forall_eq] using hsep)
          (by change 1024≤2^64;decide) (by change 8*k+j<1024;omega)
      obtain ⟨hf',hb'⟩ := Written.step hf hb hw (by omega) (by decide : 1024<2^64)
      refine ⟨⟨?_,?_,?_,(ku.trans kt).mono (by simp),hf',?_⟩,?_⟩
      · rw [t0,e0,show (8:BitVec 64)=BitVec.ofNat 64 8 by rfl,ptr_add,Nat.mul_succ]
      · rw [t1,e1,show (8:BitVec 64)=BitVec.ofNat 64 8 by rfl,ptr_add,Nat.mul_succ]
      · rw [t2,e2,ofNat_sub_one hk]
      · simpa only [Nat.mul_succ] using hb'
      · rw [t2,e2,ofNat_sub_one hk,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
        omega
  · exact ⟨by simpa only [Nat.mul_zero,VG.Proof.MlKem.AArch64.ptr_zero] using h0,
      by simpa only [Nat.mul_zero,VG.Proof.MlKem.AArch64.ptr_zero] using h1,
      h2,ka.keep.mono (by simp),by rw [ka.mem];exact Frame.refl _ _,by intro j hj;omega⟩
  · refine ⟨?_,hf,kt⟩
    simp only [bytesAt]
    exact List.map_congr_left fun i hi=>hb i (List.mem_range.mp hi)

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedMaskCopy.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.Sign

/-- The odd mask awaiting consumption in attempt `t`. -/
def Mask (p : Params) (σ : State) (t : Nat) (s : State) : Prop :=
  PolyIs s.mem (pa s t4P) (Yv p σ (p.ℓ*t) (p.ℓ-1))

def copyChk (p : Params) : Bool :=
  Sign.copyChk (sgR p) (sgW p) (yP p (p.ℓ-1)) t4P 1024 &&
    positiveIcmChk p [(yP p (p.ℓ-1),1024)] (p.ℓ-1)

theorem copyChk_ok {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87) : copyChk p=true := by
  rcases hp with rfl|rfl <;> decide

theorem copyMask_phase_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hc : copyChk p=true) (h : PositiveICm p S σ t (p.ℓ-1) s) (hm : Mask p σ t s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.copyMask p) s fun u=>
      PositiveICm p S σ t (p.ℓ-1) u ∧
      Fam u (yBase p) (p.ℓ-1+1) (Yv p σ (p.ℓ*t)) := by
  simp only [copyChk,Sign.copyChk,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hw,hi⟩,hs⟩,_⟩,_⟩,hstep⟩ := hc
  refine WP.mono_syms (copyMask_ok p s (h.l.st.lay.inR hi) (h.l.st.lay.inW hw)
    (h.l.st.lay.disj hs)) fun u ⟨hb,hf,hk⟩ hy=>?_
  have hu : PPostB S s u [(yP p (p.ℓ-1),1024)] := postB_of_keep hk (by decide) hf
  have hU := h.step hu hy hstep
  refine ⟨hU,hU.y.snoc ?_⟩
  show PolyIs _ _ _
  rw [hu.pa (pS_bases _)]
  exact polyIs_of_bytes hb hm

end VG.Proof.MlDsa.AArch64.Sign.Cached

end
