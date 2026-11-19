module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentHash
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedCommitment
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentPack
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailBody
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Parity
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Top
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CommitTail
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CommitTail
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecodeTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecodeTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWritten
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedMasks
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedCommitment
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWritten
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedMasks
meta import VerifiedGarbage.Proof.MlDsa.Sign.Mem

/-! ### `MlDsa.AArch64.Sign.CachedMaskPrefixTailTiming`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Sign.CachedMaskTail`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Sign.CachedMaskCopy`, which this module and modules that import it used -/

section

/-! ## From `CachedCopyBody.lean` -/

@[expose] public section

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
      exact inRegions_sub hin (by omega_using [hk]) (by omega_using [])
    · rw [ku.wr,e0]
      exact inRegions_sub hout (by omega_using [hk]) (by omega_using [])
    · have hw : Written u.mem t.mem (dst+BitVec.ofNat 64 (8*k)) 8
          (fun j=>s.mem (src+BitVec.ofNat 64 (8*k+j))) := by
        rw [hm,e0]
        refine (written_word u.mem _ 8 (u.mem.readW (u.gpr .x1) 64)).congr fun j hj=>?_
        rw [e1]
        simp only [Mem.readW,BitVec.setWidth_eq]
        rw [Mem.extractLsb'_read _ _ hj,ptr_add]
        exact hf.bytes (R:=⟨src,1024⟩) (by simpa only [List.mem_singleton,forall_eq] using hsep)
          (by change 1024≤2^64;decide) (by change 8*k+j<1024;omega_using [hk, hj])
      obtain ⟨hf',hb'⟩ := Written.step hf hb hw (by omega_using [hk]) (by decide : 1024<2^64)
      refine ⟨⟨?_,?_,?_,(ku.trans kt).mono (by simp),hf',?_⟩,?_⟩
      · rw [t0,e0,show (8:BitVec 64)=BitVec.ofNat 64 8 by rfl,ptr_add,Nat.mul_succ]
      · rw [t1,e1,show (8:BitVec 64)=BitVec.ofNat 64 8 by rfl,ptr_add,Nat.mul_succ]
      · rw [t2,e2,ofNat_sub_one hk]
      · simpa only [Nat.mul_succ] using hb'
      · rw [t2,e2,ofNat_sub_one hk,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [])]
        omega_using [hk]
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

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Proof.MlKem.AArch64 (Only wp_ldrx wp_nil)

theorem tailMask_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87) {σ s : State} {t : Nat}
    (h : PositiveICm p S σ t (p.ℓ-1) s) (hm : t=0 ∨ Mask p σ t s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.tailMask P p) s (PositiveICm p S σ t p.ℓ) := by
  have hlen : p.ℓ-1+1=p.ℓ := by rcases hp with rfl|rfl <;> decide
  have hk : inB (sgB p) (sc oKAP) 8=true := by rcases hp with rfl|rfl <;> decide
  have hload : WP isa (.block [.ldr .x .x9 .x28 oKAP]) s fun a=>
      Only [.x9] s a ∧ a.gpr .x9=s.mem.readW (pa s (sc oKAP)) 64 :=
    wp_ldrx (t:=.x9) (n:=.x28) (off:=oKAP) (a:=pa s (sc oKAP)) (by decide) rfl (h.l.st.lay.inR hk) fun a ha va=>wp_nil ⟨ha,va⟩
  unfold Impl.MlDsa.AArch64.Sign.Cached.tailMask
  refine WP.seq (WP.mono_syms hload fun a ⟨ha,va⟩ hya=>?_)
  have hpost : PPostB S s a [] := postB_of_keep ha.keep (by decide) (by rw [ha.mem];exact Frame.refl _ _)
  have hA := h.step hpost hya (by rcases hp with rfl|rfl <;> decide)
  have hmA : t=0 ∨ Mask p σ t a := hm.elim Or.inl fun hh=>Or.inr (by
    unfold Mask at hh ⊢
    rw [ha.mem,hpost.pa (pS_bases _)]
    exact hh)
  refine WP.seq (WP.ite (M:=isa) (a.gpr .x9 != 0) rfl (fun he=>?_) fun _=>?_)
  · have hc : Mask p σ t a := hmA.resolve_left (by
      intro hz
      rw [va,h.l.kap,hz,Nat.mul_zero] at he
      exact absurd he (by decide))
    refine WP.mono (copyMask_phase_ok (copyChk_ok hp) hA hc) fun u ⟨hu,hy⟩=>?_
    have cf : positiveFinishChk p (p.ℓ-1+1) (p.ℓ-1)=true := by rcases hp with rfl|rfl <;> decide
    have hf := WP.mono (positiveFinish_ok (by omega_using []) cf hu hy) fun _ hh=>hh.1
    simpa only [hlen] using hf
  · have cf : positiveMaskChk p (p.ℓ-1)=true := by rcases hp with rfl|rfl <;> decide
    have hf := positiveMaskR_ok hP cf hA
    unfold Impl.MlDsa.AArch64.Sign.Optimized.maskR at hf
    have hh := WP.seq_iff.mp (WP.assoc' hf)
    simpa only [hlen] using hh

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

end

/-! ## From `CachedMaskPrefix.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc seqR)
open VG.Proof.MlDsa.Sign
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Optimized

theorem cache_keep {p : Params} {S : Nat} {σ s u : State} {t : Nat}
    (L : Lay S (sgR p) (sgW p) s) (h : t=0 ∨ Mask p σ t s)
    {ws : List (Ptr×Nat)} (hP : PPostB S s u ws)
    (hc : keepB (sgR p) (sgW p) ws t4P 1024=true) : t=0 ∨ Mask p σ t u := by
  rcases h with h|h
  · exact .inl h
  · exact .inr (L.keepPoly hP hc h)

def pairCacheChk (p : Params) (r : Nat) : Bool :=
  keepB (sgR p) (sgW p) (pairSeedWrites 0) t4P 1024 &&
  keepB (sgR p) (sgW p) (pairSeedWrites 1) t4P 1024 &&
  keepB (sgR p) (sgW p) [(yP p r,1024),(yP p (r+1),1024),(sc (oR4 p),8192)] t4P 1024 &&
  keepB (sgR p) (sgW p) [(yhP p r,1024)] t4P 1024 &&
  keepB (sgR p) (sgW p) [(yhP p (r+1),1024)] t4P 1024

theorem pairCacheChk_ok {p : Params} (hp : p=mlDsa65∨p=mlDsa87) :
    (List.range (p.ℓ/2)).all (fun j => pairCacheChk p (2*j))=true := by
  rcases hp with rfl|rfl <;> decide

theorem finishCached_ok {p : Params} {S : Nat} {σ s : State} {t n r : Nat}
    (hr : r<n) (hc : positiveFinishChk p n r=true) (h : PositiveICm p S σ t r s)
    (hy : Fam s (yBase p) n (Yv p σ (p.ℓ*t))) (hm : t=0 ∨ Mask p σ t s)
    (hk : keepB (sgR p) (sgW p) [(yhP p r,1024)] t4P 1024=true) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.maskFinish p r) s fun u =>
      (PositiveICm p S σ t (r+1) u ∧ Fam u (yBase p) n (Yv p σ (p.ℓ*t))) ∧
      (t=0 ∨ Mask p σ t u) := by
  have hw := positiveFinish_ok hr hc h hy
  simp only [positiveFinishChk,optimizedMaskChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ho,hi⟩,hout⟩,hd⟩,_⟩,_⟩,_⟩,_⟩ := hc
  have hf : PolyIs s.mem (pa s (yP p r)) (Yv p σ (p.ℓ*t) r) := hy r hr
  have ht : ForwardRoots s (pa s (yhP p r)) :=
    ⟨h.l.k.d.roots.nttTableAt (h.l.st.lay.inW hout),h.l.k.d.roots.forward.readable⟩
  obtain ⟨tr,u,he,hu⟩ := hw
  obtain ⟨tr',u',he',hu'⟩ := positiveNttOutAt_layout h.l.st.lay ho hi hout hd ht hf.1
  obtain ⟨_,rfl⟩ := Exec.det he he'
  exact ⟨tr,u,he,hu,cache_keep h.l.st.lay hm hu'.1 hk⟩

theorem pairCached_ok {D : Nat}
    {nm : String} {cd : Prog isa} (C : CalleeOk D cd (expandMaskPairContract AArch64.abi D))
    {p : Params} {σ s : State} {t r : Nat} (hc : positivePairStepChk p r=true)
    (h : PositiveICm p D σ t r s) (hm : t=0 ∨ Mask p σ t s)
    (hcache : pairCacheChk p r=true) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.maskPairR p nm cd r) s (fun u => PositiveICm p D σ t (r+2) u ∧ (t=0 ∨ Mask p σ t u)) := by
  simp only [pairCacheChk,Bool.and_eq_true,and_assoc] at hcache
  obtain ⟨ck0,ck1,ckc,ckf0,ckf1⟩ := hcache
  simp only [positivePairStepChk,Bool.and_eq_true,and_assoc,decide_eq_true_eq] at hc
  obtain ⟨cs0,cs1,ck,cm,ci,cf0,cf1,hg⟩ := hc
  unfold Impl.MlDsa.AArch64.Sign.Optimized.maskPairR
  refine WP.seq (WP.mono (positivePairSeed_ok cs0 h) fun a ⟨hA,hpa,ha⟩ => ?_)
  have ma := cache_keep h.l.st.lay hm hpa ck0
  refine WP.seq (WP.mono (positivePairSeed_ok cs1 hA) fun b ⟨hB,hb,hseed1⟩ => ?_)
  have mb := cache_keep hA.l.st.lay ma hb ck1
  have hseed0 : bytesAt b.mem (pa b (sc oMP)) 66=
      rppOf p σ++integerToBytes (p.ℓ*t+r) 2 := by
    have hkeep := hA.l.st.lay.keepBytes hb ck
    simp only [Nat.mul_zero,Nat.add_zero] at ha
    rw [hkeep]
    exact ha
  have hseed1' : bytesAt b.mem (pa b (sc oMP)+66) 66=
      rppOf p σ++integerToBytes (p.ℓ*t+(r+1)) 2 := by
    change bytesAt b.mem (pa b (sc (oMP+66))) 66=_ at hseed1
    rw [← pa_sc_add] at hseed1
    exact hseed1
  refine WP.seq (WP.mono_syms (maskPairAt_ok hB.l.st.lay.s64 C hB.l.st.lay cm hg)
    fun c ⟨hcP,_,hy0,hy1⟩ hsy => ?_)
  rw [hseed0] at hy0
  rw [hseed1'] at hy1
  have mc := cache_keep hB.l.st.lay mb hcP ckc
  have hC := hB.step hcP hsy ci
  have hy : Fam c (yBase p) (r+2) (Yv p σ (p.ℓ*t)) := by
    refine Fam.snoc (Fam.snoc hC.y ?_) ?_
    · show PolyIs _ _ _
      rw [hcP.pa (pS_bases _)]
      exact hy0
    · show PolyIs _ _ _
      rw [hcP.pa (pS_bases _)]
      exact hy1
  refine WP.seq (WP.mono (finishCached_ok (by omega_using []) cf0 hC hy mc ckf0) fun d ⟨⟨hD,hyD⟩,md⟩ => ?_)
  exact WP.mono (finishCached_ok (by omega_using []) cf1 hD hyD md ckf1) fun _ hu => ⟨hu.1.1,hu.2⟩


theorem prefix_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65∨p=mlDsa87) {σ s : State} {t : Nat}
    (h : PositiveIL p S σ t s) (hm : t=0 ∨ Mask p σ t s) :
    WP isa (seqR (fun j => Impl.MlDsa.AArch64.Sign.Optimized.maskPairR p
      "vg_mldsa_expand_mask_pair_sha3" P.expandMaskPair (2*j)) 0 (p.ℓ/2)) s fun u =>
      PositiveICm p S σ t (2*(p.ℓ/2)) u ∧ (t=0 ∨ Mask p σ t u) := by
  have h3 : Ok3 p := hp.elim (fun h => .inr (.inl h)) (fun h => .inr (.inr h))
  have hc := positiveMasksChk_ok h3
  simp only [positiveMasksChk,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hc
  have hk := pairCacheChk_ok hp
  simp only [List.all_eq_true,List.mem_range] at hk
  simpa only [Nat.zero_add] using
    seqR_ok (I := fun j u => PositiveICm p S σ t (2*j) u ∧ (t=0 ∨ Mask p σ t u))
      (p.ℓ/2) 0 (fun j _ hj u hu => by
        simpa only [Nat.mul_add,Nat.mul_one] using
          pairCached_ok hP.expandMaskPair (hc.1 j (by omega_using [hj])) hu.1 hu.2 (hk j (by omega_using [hj])))
      s ⟨⟨h,fun _ h => by omega,fun _ h => by omega⟩,hm⟩

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedMaskPrefixTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (seqR)

theorem pairCached_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} {r t : Nat}
    (hc : positivePairStepChk p r=true) (hk : pairCacheChk p r=true) {E : State→State→Prop} :
    RelCT isa (RootRS p S E fun σ s => PositiveICm p S σ t r s ∧ (t=0 ∨ Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Optimized.maskPairR p "vg_mldsa_expand_mask_pair_sha3" P.expandMaskPair r)
      (RootRS p S E fun σ s => PositiveICm p S σ t (r+2) s ∧ (t=0 ∨ Mask p σ t s)) := by
  apply liftRootR (fun _ _ _ h => pairCached_ok hP.expandMaskPair hc h.1 h.2 hk)
  apply RelCT.mono (positivePairR_tr hP.expandMaskPair hc (t := t) (E := E))
  · intro x y h
    exact ⟨h.1.mono (fun _ _ h => h) (fun _ _ h => h.1),h.2.1⟩
  · intro _ _ _
    trivial

theorem prefix_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65∨p=mlDsa87) {t : Nat} {E : State→State→Prop} :
    RelCT isa (RootRS p S E fun σ s => PositiveIL p S σ t s ∧ (t=0 ∨ Mask p σ t s))
      (seqR (fun j => Impl.MlDsa.AArch64.Sign.Optimized.maskPairR p
        "vg_mldsa_expand_mask_pair_sha3" P.expandMaskPair (2*j)) 0 (p.ℓ/2))
      (RootRS p S E fun σ s => PositiveICm p S σ t (2*(p.ℓ/2)) s ∧ (t=0 ∨ Mask p σ t s)) := by
  have h3 : Ok3 p := hp.elim (fun h => .inr (.inl h)) (fun h => .inr (.inr h))
  have hc := positiveMasksChk_ok h3
  simp only [positiveMasksChk,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hc
  have hk := pairCacheChk_ok hp
  simp only [List.all_eq_true,List.mem_range] at hk
  refine RelCT.mono (seqR_tr (Q := fun j => RootRS p S E fun σ s =>
    PositiveICm p S σ t (2*j) s ∧ (t=0 ∨ Mask p σ t s)) (p.ℓ/2) 0 (fun j _ hj => ?_))
    (fun _ _ h => h.mono (fun _ _ h => ⟨⟨h.1,fun _ h => by omega,fun _ h => by omega⟩,h.2⟩))
    (fun _ _ h => by simpa only [Nat.zero_add] using h)
  simpa only [Nat.mul_add,Nat.mul_one] using pairCached_tr hP (hc.1 j (by omega_using [hj])) (hk j (by omega_using [hj])) (t := t) (E := E)

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedMaskPrefixTailTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc seqR)
open VG.Proof.MlKem.AArch64 (Only wp_ldrx wp_nil)
open VG.Proof.MlDsa.Sign

private theorem seqIte_tr {P Q : State→State→Prop} {c : Cond} {a b d : Prog isa}
    (hc : ∀x y,P x y→isa.eval c x=isa.eval c y)
    (ha : RelCT isa (fun x y=>P x y ∧ isa.eval c x=some true) (.seq a d) Q)
    (hb : RelCT isa (fun x y=>P x y ∧ isa.eval c x=some false) (.seq b d) Q) :
    RelCT isa P (.seq (.ite c a b) d) Q := by
  intro x y tx ty u v hp ex ey
  have hcond := hc x y hp
  cases ex with
  | seq ex ed =>
    cases ey with
    | seq ey ef =>
      cases ex with
      | iteT hx ea =>
        cases ey with
        | iteT _ eb =>
          obtain ⟨he,hq⟩ := ha _ _ _ _ _ _ ⟨hp,hx⟩ (.seq ea ed) (.seq eb ef)
          exact ⟨by simpa only [List.cons_append] using congrArg (List.cons (.branch true)) he,hq⟩
        | iteF hy _ => rw [hcond,hy] at hx; cases hx
      | iteF hx ea =>
        cases ey with
        | iteT hy _ => rw [hcond,hy] at hx; cases hx
        | iteF _ eb =>
          obtain ⟨he,hq⟩ := hb _ _ _ _ _ _ ⟨hp,hx⟩ (.seq ea ed) (.seq eb ef)
          exact ⟨by simpa only [List.cons_append] using congrArg (List.cons (.branch false)) he,hq⟩

theorem loadIndex_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : p=mlDsa65∨p=mlDsa87) (h : PositiveICm p S σ t (p.ℓ-1) s) (hm : t=0∨Mask p σ t s) :
    WP isa (.block [.ldr .x .x9 .x28 oKAP]) s fun u =>
      (PositiveICm p S σ t (p.ℓ-1) u ∧ (t=0∨Mask p σ t u)) ∧ u.gpr .x9=BitVec.ofNat 64 (p.ℓ*t) := by
  have hk : inB (sgB p) (sc oKAP) 8=true := by rcases hp with rfl|rfl <;> decide
  have hload : WP isa (.block [.ldr .x .x9 .x28 oKAP]) s fun a =>
      Only [.x9] s a ∧ a.gpr .x9=s.mem.readW (pa s (sc oKAP)) 64 :=
    wp_ldrx (t:=.x9) (n:=.x28) (off:=oKAP) (a:=pa s (sc oKAP))
    (by decide) rfl (h.l.st.lay.inR hk) fun a ha va=>wp_nil ⟨ha,va⟩
  refine WP.mono_syms hload fun u ⟨hu,hv⟩ hy => ?_
  have hP : PPostB S s u [] := postB_of_keep hu.keep (by decide) (by rw [hu.mem];exact Frame.refl _ _)
  exact ⟨⟨h.step hP hy (by rcases hp with rfl|rfl <;> decide),
    cache_keep h.l.st.lay hm hP (by rcases hp with rfl|rfl <;> decide)⟩,hv.trans h.l.kap⟩

theorem copyFinish_tr {p : Params} {S t : Nat} {E : State→State→Prop}
    (hp : p=mlDsa65∨p=mlDsa87) :
    RelCT isa (RootRS p S E fun σ s => PositiveICm p S σ t (p.ℓ-1) s ∧ Mask p σ t s)
      (.seq (Impl.MlDsa.AArch64.Sign.Cached.copyMask p)
        (Impl.MlDsa.AArch64.Sign.Optimized.maskFinish p (p.ℓ-1))) fun _ _ => True := by
  apply RelCT.seq (R := RootRS p S E fun σ s => PositiveICm p S σ t (p.ℓ-1) s ∧
    Fam s (yBase p) (p.ℓ-1+1) (Yv p σ (p.ℓ*t)))
  · apply liftRootR (fun _ _ _ h => copyMask_phase_ok (copyChk_ok hp) h.1 h.2)
    exact lrel_tr (hc := copyHint) (fun _ _ h=>h.1.lrel (fun _ _ h=>h.1.l.st)) (by rcases hp with rfl|rfl <;> taint_decide)
  · apply optimizedMaskFinish_tr (S := S) (show optimizedMaskChk p (p.ℓ-1)=true from by rcases hp with rfl|rfl <;> decide)
    intro x y h
    have L := h.1.lrel (fun _ _ h=>h.1.l.st)
    obtain ⟨σ,τ,_,_,_,_,ix,iy⟩ := h.1
    exact ⟨⟨σ,ix.1.l.st,ix.1.l.k.d.roots⟩,⟨τ,iy.1.l.st,iy.1.l.k.d.roots⟩,
      (ix.2 (p.ℓ-1) (by omega_using [])).1,(iy.2 (p.ℓ-1) (by omega_using [])).1,
      L.regs .x28 (by decide),L.sp,h.2.1⟩

private theorem assocBack {P Q : State→State→Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro x y tx ty u v hp ex ey
  cases ex with
  | seq ex ec =>
    cases ex with
    | seq ea eb =>
      cases ey with
      | seq ey fc =>
        cases ey with
        | seq fa fb =>
          obtain ⟨ht,hq⟩ := h _ _ _ _ _ _ hp (.seq ea (.seq eb ec)) (.seq fa (.seq fb fc))
          exact ⟨by simpa only [List.append_assoc] using ht,hq⟩

theorem tailMask_tr {P : Prims} {S t : Nat} {E : State→State→Prop}
    (hP : PrimsOk P S) {p : Params} (hp : p=mlDsa65∨p=mlDsa87) :
    RelCT isa (RootRS p S E fun σ s=>PositiveICm p S σ t (p.ℓ-1) s ∧ (t=0∨Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.tailMask P p)
      (RootRS p S E (PositiveICm p S · t p.ℓ)) := by
  apply liftRootR (fun _ _ _ h=>tailMask_ok hP hp h.1 h.2)
  unfold Impl.MlDsa.AArch64.Sign.Cached.tailMask
  apply RelCT.seq (R := RootRS p S E fun σ s=>
    (PositiveICm p S σ t (p.ℓ-1) s ∧ (t=0∨Mask p σ t s)) ∧ s.gpr .x9=BitVec.ofNat 64 (p.ℓ*t))
  · apply liftRootR (fun _ _ _ h=>loadIndex_ok hp h.1 h.2)
    exact lrel_tr (fun _ _ h=>h.1.lrel (fun _ _ h=>h.1.l.st)) (by taint_decide)
  · apply seqIte_tr
    · intro x y h
      obtain ⟨σ,τ,_,_,_,_,hx,hy⟩ := h.1
      change some (x.gpr .x9 != 0)=some (y.gpr .x9 != 0)
      rw [hx.2,hy.2]
    · apply RelCT.mono (copyFinish_tr hp)
      intro x y h
      apply RootRS.mono h.1
      intro σ s hs
      refine ⟨hs.1.1,hs.1.2.resolve_left ?_⟩
      intro ht
      obtain ⟨σ',τ,_,_,_,_,hx,_⟩ := h.1.1
      have he := h.2
      change some (x.gpr .x9 != 0)=some true at he
      rw [hx.2,ht,Nat.mul_zero] at he
      cases he
      · intro _ _ _; trivial
    · have cf : positiveMaskChk p (p.ℓ-1)=true := by rcases hp with rfl|rfl <;> decide
      apply assocBack
      apply RelCT.mono (positiveMaskR_tr hP cf)
      · intro x y h
        exact ⟨h.1.1.mono (fun _ _ h=>h) (fun _ _ hs=>hs.1.1),h.1.2.1⟩
      · intro _ _ _; trivial

theorem masks_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65∨p=mlDsa87) {σ s : State} {t : Nat}
    (h : PositiveIL p S σ t s) (hm : t=0∨Mask p σ t s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.masks P p) s (PositiveICm p S σ t p.ℓ) := by
  have hn : 2*(p.ℓ/2)=p.ℓ-1 := by rcases hp with rfl|rfl <;> decide
  unfold Impl.MlDsa.AArch64.Sign.Cached.masks
  refine WP.seq (WP.mono (prefix_ok hP hp h hm) fun u hu=>?_)
  rw [hn] at hu
  exact tailMask_ok hP hp hu.1 hu.2

theorem masks_tr {P : Prims} {S t : Nat} {E : State→State→Prop}
    (hP : PrimsOk P S) {p : Params} (hp : p=mlDsa65∨p=mlDsa87) :
    RelCT isa (RootRS p S E fun σ s=>PositiveIL p S σ t s ∧ (t=0∨Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.masks P p)
      (RootRS p S E (PositiveICm p S · t p.ℓ)) := by
  have hn : 2*(p.ℓ/2)=p.ℓ-1 := by rcases hp with rfl|rfl <;> decide
  unfold Impl.MlDsa.AArch64.Sign.Cached.masks
  have hf := prefix_tr (E:=E) (t:=t) hP hp
  rw [hn] at hf
  exact RelCT.seq hf (tailMask_tr hP hp)

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

end

end

/-! ### `MlDsa.AArch64.Sign.CachedHashSetup`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Proof.MlKem.AArch64 (Only wp_ldrx wp_addImm wp_nil)

/-- Exact first block of `Cached.hash`; only x9 changes. -/
theorem hashSetup_run {p : Params} (hp : Ok3 p) (s : State)
    (hr : InRegions (s.rd++s.wr) (pa s (sc oKAP)) 8) :
    WP isa (.block [.ldr .x .x9 .x28 oKAP,.addImm .x .x9 .x9 (2*p.ℓ-1)]) s fun u=>
      Only [.x9] s u ∧ u.gpr .x9=s.mem.readW (pa s (sc oKAP)) 64+BitVec.ofNat 64 (2*p.ℓ-1) := by
  have himm : 2*p.ℓ-1<4096 := by rcases hp with rfl|rfl|rfl <;> decide
  refine wp_ldrx (a:=pa s (sc oKAP)) (by decide) rfl hr fun a ha ea=>
    wp_addImm himm fun b hb eb=>wp_nil ⟨(ha.trans hb).mono (by simp),?_⟩
  rw [eb,ea]

/-- The counter used by the fused commitment/mask helper is the next
iteration's odd-mask index. No truncation or extra loop-range assumption is
needed for this exact 64-bit equality. -/
theorem hashSetup_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (h : PositiveICh p S σ t p.k s) :
    WP isa (.block [.ldr .x .x9 .x28 oKAP,.addImm .x .x9 .x9 (2*p.ℓ-1)]) s fun u=>
      PositiveICh p S σ t p.k u ∧
      u.gpr .x9=BitVec.ofNat 64 (p.ℓ*t+2*p.ℓ-1) ∧ Only [.x9] s u := by
  have hr : inB (sgB p) (sc oKAP) 8=true := by rcases hp with rfl|rfl|rfl <;> decide
  have hk : icwChk p [] p.k=true := by rcases hp with rfl|rfl|rfl <;> decide
  have hw1 : keepB (sgR p) (sgW p) [] (sc oW1) (w1Len p*p.k)=true := by
    rcases hp with rfl|rfl|rfl <;> decide
  have L := h.c.masks.l.st.lay
  refine WP.mono_syms (hashSetup_run hp s (L.inR hr)) fun u ⟨hu,hv⟩ hy=>?_
  have hpu : PPostB S s u [] := postB_of_keep hu.keep (by decide) (by rw [hu.mem]; exact Frame.refl _ _)
  refine ⟨⟨h.c.step hpu hy hk (by simp),?_⟩,?_,hu⟩
  · rw [L.keepBytes hpu hw1,h.w1]
  · rw [hv,h.c.masks.l.kap,ofNat64_add]
    apply congrArg (BitVec.ofNat 64)
    have hl : 1≤2*p.ℓ := by rcases hp with rfl|rfl|rfl <;> decide
    omega_using [hl]

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

end

/-! ### `MlDsa.AArch64.Sign.CachedHashCall`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Sign.CommitTailTiming`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64

/-- Both absorbed streams remain secret. Only the six buffer pointers
influence the helper's fixed memory trace. The nonce value is not public. -/
theorem code65_ct :
    ConstantTime isa (fun _=>True)
      (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x6]))
      (Impl.MlDsa.AArch64.Sign.CommitTail.code 768 48) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x6])
    (fun _ _ _ _ h=>h) (by taint_decide)

/-- The longer commitment uses the same secret-input trace policy. -/
theorem code87_ct :
    ConstantTime isa (fun _=>True)
      (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x6]))
      (Impl.MlDsa.AArch64.Sign.CommitTail.code 1024 64) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x6])
    (fun _ _ _ _ h=>h) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

end

/-! ### `MlDsa.CommitTailContract`, which this module and modules that import it used -/

section

/-!
# ML-DSA: the contract of the tail of the signing commitment

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

/-- A standard commitment hash and an independent next-attempt mask seed.
The two sponge streams are evaluated together without changing either result. -/
def commitTailSig (wlen olen : Nat) : Sig where
  params := [("mu",.array false .u8 64),("w1",.array false .u8 wlen),
    ("commitment",.array true .u8 olen),("scratch",.array true .u64 256),
    ("seed",.array false .u8 64),("nonce",.int .u64 false),("mask",.array true .u32 256)]

def commitTailSeed (m : Mem) (seed : Addr) (nonce : BitVec 64) : List Byte :=
  Spec.Sha3.bytesAt m seed 64 ++ [nonce.extractLsb' 0 8,nonce.extractLsb' 8 8]

def commitTailContract {M : ISA} (A : Abi M) (wlen olen : Nat) (stack : Nat := 0) : Contract M :=
  (commitTailSig wlen olen).contract A
    (post := fun mu w1 commitment _scratch seed nonce mask m m' _ =>
      Spec.Sha3.bytesAt m' commitment olen =
        H (Spec.Sha3.bytesAt m mu 64 ++ Spec.Sha3.bytesAt m w1 wlen) olen ∧
      PolyIs m' mask (toRq (bitUnpack (H (commitTailSeed m seed nonce) 640) 524287 524288)))
    (writeArgs := true) (stack := stack)

end VG.Proof.MlDsa

end

end

/-! ### `MlDsa.AArch64.Sign.CommitTailVerified`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Sign.CommitTailCorrect`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Sign.CommitTailEpi`, which only this module used -/

section

/-! ## From `CommitTailRestoreV.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_ldrq)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Restores every nonvolatile vector from the untouched save area. -/
theorem restoreV_ok {σ s : State} (hs : Saved σ s.mem) (hptr : s.gpr .x3=σ.gpr .x3)
    (hin : ∀i<8, InRegions (s.rd++s.wr) (σ.gpr .x3+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block restore) s fun t => RegKeep [] s t ∧ t.mem=s.mem ∧
      ∀i<8,t.v (vreg (8+i))=σ.v (vreg (8+i)) := by
  unfold restore
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M:=isa)
    (fun k t => RegKeep [] s t ∧ t.mem=s.mem ∧ ∀i<k,t.v (vreg (8+i))=σ.v (vreg (8+i)))
    (fun k t hk ht => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,fun _ h => by omega⟩
  refine wp_ldrq ⟨by omega_using [],by omega_using [hk]⟩ (by rw [ht.1.gpr .x3 (by simp),hptr])
    (by rw [ht.1.rd,ht.1.wr]; exact hin k hk) fun u hu => WP.block_nil_iff.mpr ?_
  refine ⟨(ht.1.trans (RegKeep.vupd hu)).mono (by simp),hu.mem.trans ht.2.1,?_⟩
  intro i hi
  by_cases he : i=k
  · subst i
    rw [hu.v,ht.2.1,hs.vec k hk]
  · have hne : vreg (8+i)≠vreg (8+k) := by
      rw [ne_eq,vreg_inj (8+i) (by omega_using [hk, hi]) (8+k) (by omega_using [hk])]; omega_using [he]
    rw [hu.get _ hne]
    exact ht.2.2 i (by omega_using [hi, he])

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailRestoreG.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

private theorem saved_mem : ∀i<4,saved[i]!∈saved := by decide
private theorem saved_inj : ∀i<4,∀j<4,saved[i]! =saved[j]! ↔ i=j := by decide

/-- Restores all four scalar saves, including the incoming return address. -/
theorem restoreG_ok {σ s : State} (hs : Saved σ s.mem) (hptr : s.gpr .x3=σ.gpr .x3)
    (hin : ∀i<4, InRegions (s.rd++s.wr) (σ.gpr .x3+BitVec.ofNat 64 (128+8*i)) 8) :
    WP isa (.block ((List.range 4).map fun i => .ldr .x saved[i]! .x3 (128+8*i))) s fun t =>
      RegKeep saved s t ∧ t.mem=s.mem ∧ t.v=s.v ∧
      ∀i<4,t.gpr saved[i]! =σ.gpr saved[i]! := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M:=isa)
    (fun k t => RegKeep saved s t ∧ t.mem=s.mem ∧ t.v=s.v ∧
      ∀i<k,t.gpr saved[i]! =σ.gpr saved[i]!)
    (fun k t hk ht => ?_) 4 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,rfl,fun _ h => by omega⟩
  refine wp_ldr ⟨by omega_using [],by omega_using [hk]⟩ (by rw [ht.1.gpr .x3 (by decide),hptr])
    (by rw [ht.1.rd,ht.1.wr]; exact hin k hk) fun u hu => WP.block_nil_iff.mpr ?_
  refine ⟨(ht.1.trans (RegKeep.upd hu)).mono ?_,hu.mem.trans ht.2.1,hu.vec.trans ht.2.2.1,?_⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hr
    · rcases List.mem_singleton.mp hr with rfl
      exact saved_mem k hk
  · intro i hi
    by_cases he : i=k
    · subst i
      rw [hu.gpr,ht.2.1,hs.regs k hk]
    · have hne : saved[i]!≠saved[k]! := by
        rw [ne_eq,saved_inj i (by omega_using [hk, hi]) k hk]; exact he
      rw [hu.other _ hne]
      exact ht.2.2.2 i (by omega_using [hi, he])

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailEpi.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_mov)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- The outer helper restores its captured nonvolatile vectors and scalar
registers without changing any result or workspace bytes. -/
theorem epi_ok {σ s : State} (hs : Saved σ s.mem) (hptr : s.gpr .x19=σ.gpr .x3)
    (hv : ∀i<8, InRegions (s.rd++s.wr) (σ.gpr .x3+BitVec.ofNat 64 (16*i)) 16)
    (hg : ∀i<4, InRegions (s.rd++s.wr) (σ.gpr .x3+BitVec.ofNat 64 (128+8*i)) 8) :
    WP isa (.block epi) s fun t =>
      RegKeep (.x3::saved) s t ∧ t.mem=s.mem ∧
      (∀i<8,t.v (vreg (8+i))=σ.v (vreg (8+i))) ∧
      (∀i<4,t.gpr saved[i]! =σ.gpr saved[i]!) := by
  unfold epi
  change WP isa (.block (Impl.MlKem.AArch64.mov .x3 .x19 ::
    (restore ++ (List.range 4).map fun i => .ldr .x saved[i]! .x3 (128+8*i)))) s _
  refine wp_mov fun a ha => ?_
  rw [WP.block_append_iff]
  refine WP.mono (restoreV_ok (by rw [ha.mem]; exact hs) (ha.gpr.trans hptr)
    (fun i hi => by rw [ha.rd,ha.wr]; exact hv i hi)) fun b ⟨hb,hmb,hvb⟩ => ?_
  refine WP.mono (restoreG_ok (by rw [hmb,ha.mem]; exact hs)
    ((hb.gpr .x3 (by simp)).trans (ha.gpr.trans hptr))
    (fun i hi => by rw [hb.rd,hb.wr,ha.rd,ha.wr]; exact hg i hi))
    fun t ⟨ht,hmt,hvt,hgt⟩ => ?_
  refine ⟨(((RegKeep.upd ha).trans hb).trans ht).mono (by simp),
    hmt.trans (hmb.trans ha.mem),?_,hgt⟩
  intro i hi
  rw [hvt]
  exact hvb i hi

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Original ABI state is restored after the shared-lane computation. -/
theorem finish_ok {σ s : State} {wlen olen : Nat} (hp : Pre wlen olen σ)
    (hs : BodyPost wlen olen σ s) :
    WP isa (.block epi) s fun t => abiPreserved σ t ∧ Frame (writes σ olen) σ.mem t.mem ∧
      Spec.Sha3.bytesAt t.mem (σ.gpr .x2) olen=Spec.MlDsa.H
        (Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) 64++Spec.Sha3.bytesAt σ.mem (σ.gpr .x1) wlen) olen ∧
      Proof.MlDsa.PolyIs t.mem (σ.gpr .x6) (Spec.MlDsa.toRq (Spec.MlDsa.bitUnpack
        (Spec.MlDsa.H (seedBytes σ.mem (σ.gpr .x4) (σ.gpr .x5)) 640) 524287 524288)) := by
  obtain ⟨hk,hsv,hf,h19,hh,hm⟩ := hs
  refine WP.mono (epi_ok hsv h19 (fun i hi => by
    rw [hk.rd,hk.wr]; exact hp.readWork _ _ (by omega_using [hi])) (fun i hi => by
    rw [hk.rd,hk.wr]; exact hp.readWork _ _ (by omega_using [hi]))) fun t ⟨ht,hmt,hv,hg⟩ => ?_
  refine ⟨⟨?_,ht.sp.trans hk.sp,?_⟩,?_,?_,?_⟩
  · intro r hr
    simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact hg 0 (by decide)
      | exact hg 1 (by decide)
      | exact hg 2 (by decide)
      | exact hg 3 (by decide)
      | exact (ht.gpr _ (by decide)).trans (hk.gpr _ (by decide))
  · intro r hr
    simp only [preservedV,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 0 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 1 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 2 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 3 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 4 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 5 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 6 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 7 (by decide))
  · rw [hmt]; exact hf
  · rw [hmt]; exact hh
  · rw [hmt]; exact hm

/-- Complete measured commitment-plus-mask helper, including save/restore. -/
theorem raw_ok (σ : State) {wlen olen : Nat} (hp : Pre wlen olen σ) :
    WP isa (code wlen olen) σ fun t => abiPreserved σ t ∧ Frame (writes σ olen) σ.mem t.mem ∧
      Spec.Sha3.bytesAt t.mem (σ.gpr .x2) olen=Spec.MlDsa.H
        (Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) 64++Spec.Sha3.bytesAt σ.mem (σ.gpr .x1) wlen) olen ∧
      Proof.MlDsa.PolyIs t.mem (σ.gpr .x6) (Spec.MlDsa.toRq (Spec.MlDsa.bitUnpack
        (Spec.MlDsa.H (seedBytes σ.mem (σ.gpr .x4) (σ.gpr .x5)) 640) 524287 524288)) := by
  obtain ⟨tf,s,hf,hs⟩ := front_ok hp.toFrontPre
  obtain ⟨tb,t,hb,ht⟩ := body_ok hp hs
  obtain ⟨te,u,he,hu⟩ := finish_ok hp ht
  cases hf with
  | seq hf0 hf1 =>
    cases hb with
    | seq hb0 hb1 =>
      exact ⟨_,_,Exec.seq hf0 (Exec.seq hf1 (Exec.seq hb0 (Exec.seq hb1 he))),hu⟩

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

end

/-! ## From `CommitTailContract.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64 VG.Spec.MlDsa

def kernel (wlen olen : Nat) : Contract isa where
  pre := Pre wlen olen
  post s t := Spec.Sha3.bytesAt t.mem (s.gpr .x2) olen=H
    (Spec.Sha3.bytesAt s.mem (s.gpr .x0) 64++Spec.Sha3.bytesAt s.mem (s.gpr .x1) wlen) olen ∧
    PolyIs t.mem (s.gpr .x6) (toRq (bitUnpack (H (seedBytes s.mem (s.gpr .x4) (s.gpr .x5)) 640) 524287 524288))
  pub := VG.AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x6])

theorem correct (s : State) {wlen olen : Nat} (hp : (kernel wlen olen).pre s) :
    ∃tr t,Exec isa (Impl.MlDsa.AArch64.Sign.CommitTail.code wlen olen) s tr t ∧
      abiPreserved s t ∧ (kernel wlen olen).post s t := by
  obtain ⟨tr,t,he,habi,_,hhash,hmask⟩ := raw_ok s hp
  exact ⟨tr,t,he,habi,hhash,hmask⟩

theorem shared_pre {s : State} {wlen olen : Nat} (hw : wlen=768 ∨ wlen=1024)
    (ho : olen=48 ∨ olen=64) (h : (commitTailContract AArch64.abi wlen olen).pre s) :
    Pre wlen olen s := by
  sig_pre [commitTailContract,commitTailSig,AArch64.abi,AArch64.argRegs] at h
  sig_split h
  have hrd : s.rd=[⟨s.gpr .x0,64⟩,⟨s.gpr .x1,wlen⟩,⟨s.gpr .x4,64⟩] := by with_reducible assumption
  have hwr : s.wr=[⟨s.gpr .x2,olen⟩,⟨s.gpr .x3,2048⟩,⟨s.gpr .x6,1024⟩] := by with_reducible assumption
  refine ⟨⟨hw,?_,?_,?_,?_,?_,?_,?_⟩,ho,?_,?_,?_,?_,?_,?_⟩
  · intro d n hn
    exact ⟨⟨s.gpr .x0,64⟩,by rw [hrd]; simp,Offset.contains_base _ hn (by omega_using [hn])⟩
  · intro d n hn
    exact ⟨⟨s.gpr .x1,wlen⟩,by rw [hrd]; simp,Offset.contains_base _ hn (by rcases hw with rfl|rfl <;> omega_using [hn])⟩
  · intro d n hn
    exact ⟨⟨s.gpr .x4,64⟩,by rw [hrd]; simp,Offset.contains_base _ hn (by omega_using [hn])⟩
  · intro d n hn
    exact ⟨⟨s.gpr .x3,2048⟩,by rw [hwr]; simp,Offset.contains_base _ hn (by omega_using [hn])⟩
  · with_reducible assumption
  · with_reducible assumption
  · exact Region.Disjoint.symm (by with_reducible assumption)
  · intro d n hn
    exact ⟨⟨s.gpr .x2,olen⟩,by rw [hwr]; simp,Offset.contains_base _ hn (by rcases ho with rfl|rfl <;> omega_using [hn])⟩
  · exact ⟨⟨s.gpr .x6,1024⟩,by rw [hwr]; simp,by simp [Region.Contains]⟩
  · intro d n hn
    exact ⟨⟨s.gpr .x3,2048⟩,by rw [hwr]; simp,Offset.contains_base _ hn (by omega_using [hn])⟩
  · with_reducible assumption
  · exact Region.Disjoint.symm (by with_reducible assumption)
  · with_reducible assumption

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64 VG.Spec.MlDsa

def satState (wlen olen : Nat) : State where
  gpr r := match r with
    | .x0=>0x1000 | .x1=>0x2000 | .x2=>0x3000 | .x3=>0x4000
    | .x4=>0x6000 | .x6=>0x7000 | _=>0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000,64⟩,⟨0x2000,wlen⟩,⟨0x6000,64⟩]
  wr := [⟨0x3000,olen⟩,⟨0x4000,2048⟩,⟨0x7000,1024⟩]

theorem implies {wlen olen : Nat} (hw : wlen=768 ∨ wlen=1024) (ho : olen=48 ∨ olen=64) :
    (kernel wlen olen).Implies (commitTailContract AArch64.abi wlen olen) := by
  refine { pre := fun _ h => shared_pre hw ho h, post := ?_,pub := ?_,sat := ?_ }
  · sig_implies_post [commitTailContract,commitTailSig,kernel,seedBytes,commitTailSeed,AArch64.abi,AArch64.argRegs]
  · intro s t _ _ h
    sig_pub [commitTailContract,commitTailSig,AArch64.abi,AArch64.argRegs] at h
    sig_split h
    refine ⟨by with_reducible assumption,?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> with_reducible assumption
  · refine ⟨satState wlen olen,?_⟩
    rcases hw with rfl|rfl <;> rcases ho with rfl|rfl
    all_goals
      sig_pre [commitTailContract,commitTailSig,AArch64.abi,AArch64.argRegs]
      sig_and_intros
    all_goals first | rfl | exact Region.disjoint_of_sep (by decide) | decide

theorem verified65 : Verified AArch64.target
    (Impl.MlDsa.AArch64.Sign.CommitTail.code 768 48) (commitTailContract AArch64.abi 768 48) :=
  Verified.of_correct (fun s hp => correct s hp) (fun s t l r a b _ _ hp hs ht => code65_ct s t l r a b trivial trivial hp hs ht)
    (implies (.inl rfl) (.inl rfl))

theorem verified87 : Verified AArch64.target
    (Impl.MlDsa.AArch64.Sign.CommitTail.code 1024 64) (commitTailContract AArch64.abi 1024 64) :=
  Verified.of_correct (fun s hp => correct s hp) (fun s t l r a b _ _ hp hs ht => code87_ct s t l r a b trivial trivial hp hs ht)
    (implies (.inr rfl) (.inr rfl))

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

end

end


/-! ## From `CommitTailCall.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64 VG.Spec.MlDsa

theorem callee65 {S : Nat} (hS : S<2^64) :
    CalleeOk S (Impl.MlDsa.AArch64.Sign.CommitTail.code 768 48)
      (commitTailContract AArch64.abi 768 48 S) :=
  CalleeOk.of_verified hS verified65 (by omega_using []) (by
    have h : (Impl.MlDsa.AArch64.Sign.CommitTail.code 768 48).aarch64Depth=0 := by decide
    rw [h]; omega_using []) (by lit_decide)

theorem callee87 {S : Nat} (hS : S<2^64) :
    CalleeOk S (Impl.MlDsa.AArch64.Sign.CommitTail.code 1024 64)
      (commitTailContract AArch64.abi 1024 64 S) :=
  CalleeOk.of_verified hS verified87 (by omega_using []) (by
    have h : (Impl.MlDsa.AArch64.Sign.CommitTail.code 1024 64).aarch64Depth=0 := by decide
    rw [h]; omega_using []) (by lit_decide)

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CachedHashPre.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc Arg)
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)

def hashReads (p : Params) (s : State) : List Region :=
  [⟨pa s (.x26,0),64⟩,⟨pa s (sc oW1),p.k*w1Len p⟩,⟨pa s (sc oMS),64⟩]
def hashWrites (p : Params) (s : State) : List Region :=
  [⟨pa s (sc oCT),cLen p⟩,⟨pa s t1P,2048⟩,⟨pa s t4P,1024⟩]

theorem hash_pre {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87) {S : Nat} {s s1 : State}
    (L : Lay S (sgR p) (sgW p) s) (h1 : Args (hashArgs p) s s1) :
    (commitTailContract abi (p.k*w1Len p) (cLen p) S).pre
      (s1.callEntry.withRegions (hashReads p s) (hashWrites p s)) := by
  sig_pre [commitTailContract,commitTailSig,AArch64.abi,VG.AArch64.argRegs]
  rw [h1.ptr (r:=.x0) (p:=(.x26,0)) (by simp [hashArgs]),
    h1.ptr (r:=.x1) (p:=sc oW1) (by simp [hashArgs]),
    h1.ptr (r:=.x2) (p:=sc oCT) (by simp [hashArgs]),
    h1.ptr (r:=.x3) (p:=t1P) (by simp [hashArgs]),
    h1.ptr (r:=.x4) (p:=sc oMS) (by simp [hashArgs]),
    h1.ptr (r:=.x6) (p:=t4P) (by simp [hashArgs]),Args.sp h1]
  simp only [hashReads,hashWrites]
  and_intros
  all_goals first
    | with_reducible rfl
    | exact True.intro
    | exact wfP_of (Lay.spS L)
    | exact resv fun _ hr=>by
        rw [stackBelow_mem hr]
        refine conj_cons (L.stkD (p:=(.x26,0)) (l:=64) (by rcases hp with rfl|rfl <;> decide)) ?_
        refine conj_cons (L.stkD (p:=sc oW1) (l:=p.k*w1Len p) (by rcases hp with rfl|rfl <;> decide)) ?_
        refine conj_cons (L.stkD (p:=sc oCT) (l:=cLen p) (by rcases hp with rfl|rfl <;> decide)) ?_
        refine conj_cons (L.stkD (p:=t1P) (l:=2048) (by rcases hp with rfl|rfl <;> decide)) ?_
        refine conj_cons (L.stkD (p:=sc oMS) (l:=64) (by rcases hp with rfl|rfl <;> decide)) ?_
        exact conj_cons (L.stkD (p:=t4P) (l:=1024) (by rcases hp with rfl|rfl <;> decide)) conj_nil
    | exact Lay.disj L (by rcases hp with rfl|rfl <;> decide)
    | exact (Lay.disj L (by rcases hp with rfl|rfl <;> decide)).symm
    | exact Lay.nwp L (by rcases hp with rfl|rfl <;> decide)

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedHashGlue.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc Arg glue)
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)
open VG.Proof.MlKem.AArch64 (Only wp_nil)

/-- The nonce lives in x9, which these seven argument moves preserve. -/
theorem hashGlue_ok (p : Params) (s : State) :
    WP isa (.block (glue (hashArgs p))) s (Args (hashArgs p) s) := by
  simp only [hashArgs,glue,Arg.instrs]
  refine lea_ok (by decide) 0 fun s0 h0 e0 => ?_
  refine lea_ok (by decide) oW1 fun s1 h1 e1 => ?_
  refine lea_ok (by decide) oCT fun s2 h2 e2 => ?_
  refine lea_ok (by decide) t1P.2 fun s3 h3 e3 => ?_
  refine lea_ok (by decide) oMS fun s4 h4 e4 => ?_
  refine lea_ok (by decide) 0 fun s5 h5 e5 => ?_
  refine lea_ok (by decide) t4P.2 fun s6 h6 e6 => ?_
  have h := (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6
  apply wp_nil
  refine ⟨⟨?_,h.mem⟩,h.keep.mono (by decide)⟩
  simp only [List.mem_cons,List.not_mem_nil,forall_eq_or_imp,false_implies,implies_true,and_true,
    Arg.val,pa]
  and_intros
  · rw [h6.get .x0 (by decide),h5.get .x0 (by decide),h4.get .x0 (by decide),
      h3.get .x0 (by decide),h2.get .x0 (by decide),h1.get .x0 (by decide),e0]
  · rw [h6.get .x1 (by decide),h5.get .x1 (by decide),h4.get .x1 (by decide),
      h3.get .x1 (by decide),h2.get .x1 (by decide),e1,h0.get .x28 (by decide)]
  · rw [h6.get .x2 (by decide),h5.get .x2 (by decide),h4.get .x2 (by decide),
      h3.get .x2 (by decide),e2,h1.get .x28 (by decide),h0.get .x28 (by decide)]
  · rw [h6.get .x3 (by decide),h5.get .x3 (by decide),h4.get .x3 (by decide),e3,
      h2.get .x28 (by decide),h1.get .x28 (by decide),h0.get .x28 (by decide)]
  · rw [h6.get .x4 (by decide),h5.get .x4 (by decide),e4,h3.get .x28 (by decide),
      h2.get .x28 (by decide),h1.get .x28 (by decide),h0.get .x28 (by decide)]
  · rw [h6.get .x5 (by decide),e5,h4.get .x9 (by decide),h3.get .x9 (by decide),
      h2.get .x9 (by decide),h1.get .x9 (by decide),h0.get .x9 (by decide)]
  · rw [e6,h5.get .x28 (by decide),h4.get .x28 (by decide),h3.get .x28 (by decide),
      h2.get .x28 (by decide),h1.get .x28 (by decide),h0.get .x28 (by decide)]

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedHashCall.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)
open VG.Impl.MlDsa.AArch64.Call (callAt)

/-- Caller rule for the measured argument moves, including the nonce in x9. -/
theorem hashCall_ok {p : Params} {S : Nat} (hS : S<2^64)
    {n : String} {c : Prog isa} {k : Contract isa} (C : CalleeOk S c k)
    {s : State} {rd wr : List Region}
    (hpre : ∀ s1, Args (hashArgs p) s s1 → k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd++wr) (s.rd++s.wr)) (hw : Covers wr s.wr) :
    WP isa (callAt n c (hashArgs p)) s fun s' => Post S s s' wr ∧
      ∃ s1, Args (hashArgs p) s s1 ∧
        k.post (s1.callEntry.withRegions rd wr) (s'.withRegions rd wr) := by
  refine WP.seq (WP.mono (hashGlue_ok p s) fun s1 h1 => ?_)
  have k1 := h1.2
  refine WP.callFV C.correct (hpre s1 h1) (by rw [k1.rd,k1.wr]; exact hc)
    (by rw [k1.wr]; exact hw)
    (fun s' hrd hwr hsp hf hcs hvcs hpost => ?_) (by have := C.fd; omega_using [hS, this])
  refine ⟨⟨hrd.trans k1.rd,hwr.trans k1.wr,hsp.trans k1.sp,
    fun r hr h30 => by rw [hcs r hr h30,k1.gpr r (argRegs_pres r hr)],?_,
    fun r hr => (hvcs r hr).trans (k1.vcs r hr)⟩,s1,h1,hpost⟩
  rw [h1.1.2,k1.sp] at hf
  exact Frame.below_mono hf C.fd hS

theorem hash_cov {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} {s : State} (L : Lay S (sgR p) (sgW p) s) :
    Covers (hashReads p s ++ hashWrites p s) (s.rd++s.wr) ∧
    Covers (hashWrites p s) s.wr := by
  have hr : Covers (hashReads p s) (s.rd++s.wr) := by
    apply Covers.cons (L.cR (p:=(.x26,0)) (l:=64) (by rcases hp with rfl|rfl <;> decide))
    apply Covers.cons (L.cR (p:=Impl.MlDsa.AArch64.Call.sc Impl.MlDsa.AArch64.Sign.oW1)
      (l:=p.k*w1Len p) (by rcases hp with rfl|rfl <;> decide))
    exact L.cR (by rcases hp with rfl|rfl <;> decide)
  have hw : Covers (hashWrites p s) s.wr := by
    apply Covers.cons (L.cW (p:=Impl.MlDsa.AArch64.Call.sc Impl.MlDsa.AArch64.Sign.oCT)
      (l:=cLen p) (by rcases hp with rfl|rfl <;> decide))
    apply Covers.cons (L.cW (p:=Impl.MlDsa.AArch64.Sign.t1P) (l:=2048)
      (by rcases hp with rfl|rfl <;> decide))
    exact L.cW (by rcases hp with rfl|rfl <;> decide)
  exact ⟨Covers.append_left hr (Covers.right hw),hw⟩

theorem hashReady_ok {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) {s : State} (L : Lay S (sgR p) (sgW p) s) :
    WP isa (callAt (if p.ℓ=5 then "vg_mldsa_commit_tail65" else "vg_mldsa_commit_tail87")
      (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*w1Len p) (cLen p)) (hashArgs p)) s
      (fun s' => Post S s s' (hashWrites p s) ∧
        ∃ s1, Args (hashArgs p) s s1 ∧
          (commitTailContract abi (p.k*w1Len p) (cLen p) S).post
            (s1.callEntry.withRegions (hashReads p s) (hashWrites p s))
            (s'.withRegions (hashReads p s) (hashWrites p s))) := by
  have C : CalleeOk S (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*w1Len p) (cLen p))
      (commitTailContract abi (p.k*w1Len p) (cLen p) S) := by
    rcases hp with rfl|rfl
    · exact CommitTail.callee65 hS
    · exact CommitTail.callee87 hS
  exact hashCall_ok hS C (fun _ h1 => hash_pre hp L h1)
    (hash_cov hp L).1 (hash_cov hp L).2

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

end

end

/-! ### `MlDsa.AArch64.Sign.CachedHashFrame`, which only this module used -/

section

/-! ## From `CachedHashPost.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)
open VG.Impl.MlDsa.AArch64.Call (sc callAt)
open VG.Spec.Sha3 (bytesAt)

abbrev hashWritePtrs (p : Params) := [(sc oCT,cLen p),(t1P,2048),(t4P,1024)]

theorem hashReady_post {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) {s : State} (L : Lay S (sgR p) (sgW p) s) :
    WP isa (callAt (if p.ℓ=5 then "vg_mldsa_commit_tail65" else "vg_mldsa_commit_tail87")
      (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*w1Len p) (cLen p)) (hashArgs p)) s
      (fun u => PPostB S s u (hashWritePtrs p) ∧
        bytesAt u.mem (pa s (sc oCT)) (cLen p)=
          H (bytesAt s.mem (pa s (.x26,0)) 64 ++
            bytesAt s.mem (pa s (sc oW1)) (p.k*w1Len p)) (cLen p) ∧
        PolyIs u.mem (pa s t4P)
          (toRq (bitUnpack (H (commitTailSeed s.mem (pa s (sc oMS)) (s.gpr .x9)) 640)
            524287 524288))) := by
  refine WP.mono (hashReady_ok hp hS L) fun u ⟨hP,s1,h1,hq⟩ => ⟨hP.b,?_⟩
  sig_post [commitTailContract,commitTailSig,AArch64.abi,VG.AArch64.argRegs] at hq
  rw [h1.ptr (r:=.x0) (p:=(.x26,0)) (by simp [hashArgs]),
    h1.ptr (r:=.x1) (p:=sc oW1) (by simp [hashArgs]),
    h1.ptr (r:=.x2) (p:=sc oCT) (by simp [hashArgs]),
    h1.ptr (r:=.x4) (p:=sc oMS) (by simp [hashArgs]),
    h1.ptr (r:=.x5) (p:=(.x9,0)) (by simp [hashArgs]),
    h1.ptr (r:=.x6) (p:=t4P) (by simp [hashArgs]),Args.mem h1] at hq
  simpa only [pa,BitVec.add_zero] using hq

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedHashFrame.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)
open VG.Impl.MlDsa.AArch64.Call (sc callAt)
open VG.Proof.MlDsa.Sign
open VG.Spec.Sha3 (bytesAt)

theorem hashFrameChk {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87) :
    icwChk p (hashWritePtrs p) p.k=true ∧
    (∀w∈hashWritePtrs p,inB (sgW p) w.1 w.2=true) := by
  rcases hp with rfl|rfl <;> decide

/-- The helper preserves the commitment inputs and produces its exact digest. -/
theorem hashReady_phase {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) {σ s : State} {t : Nat}
    (h : PositiveICh p S σ t p.k s) :
    WP isa (callAt (if p.ℓ=5 then "vg_mldsa_commit_tail65" else "vg_mldsa_commit_tail87")
      (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*w1Len p) (cLen p)) (hashArgs p)) s
      (fun u => PositiveIC p S σ t u ∧
        PolyIs u.mem (pa u t4P)
          (toRq (bitUnpack (H (commitTailSeed s.mem (pa s (sc oMS)) (s.gpr .x9)) 640)
            524287 524288))) := by
  refine WP.mono_syms (hashReady_post hp hS h.c.masks.l.st.lay)
    fun u ⟨hP,hct,hm⟩ hy => ⟨⟨h.c.step hP hy (hashFrameChk hp).1 (hashFrameChk hp).2,?_⟩,?_⟩
  · rw [hP.pa (by decide),hct,Nat.mul_comm p.k,h.w1,h.c.masks.l.st.mu]
    simp only [CTv,ctF,w1Encode,List.flatMap_map]
  · rw [hP.pa (by decide)]
    exact hm

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

end

end


-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Sign/CachedHashNonce.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.Sign

/-- The cached stream is the final polynomial of the next attempt. -/
theorem nextNonce {p : Params} (hp : p=mlDsa65∨p=mlDsa87) (t : Nat) :
    p.ℓ*t+2*p.ℓ-1=p.ℓ*(t+1)+(p.ℓ-1) := by
  rcases hp with rfl|rfl <;> simp only [mlDsa65,mlDsa87] <;> omega

theorem nextNonce_bound {p : Params} (hp : p=mlDsa65∨p=mlDsa87) {t : Nat} (ht : t<814) :
    p.ℓ*t+2*p.ℓ-1<2^16 := by
  rcases hp with rfl|rfl <;> simp only [mlDsa65,mlDsa87] <;> omega

theorem nonceExtract_bytes {n : Nat} (hn : n<2^16) :
    [(BitVec.ofNat 64 n).extractLsb' 0 8,(BitVec.ofNat 64 n).extractLsb' 8 8]=integerToBytes n 2 := by
  have h := kappa_bytes hn
  have h0 (v : BitVec 64) : v.extractLsb' 0 8=v.setWidth 8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat,BitVec.toNat_setWidth]
    rfl
  have h1 (v : BitVec 64) : v.extractLsb' 8 8=(v >>> 8).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat,BitVec.toNat_setWidth,BitVec.toNat_ushiftRight]
  rw [h0,h1]
  exact h

theorem nextSeed {p : Params} (hp : p=mlDsa65∨p=mlDsa87) {t : Nat} (ht : t<814)
    {m : Mem} {a : Addr} {σ : State} {nonce : BitVec 64}
    (hs : Spec.Sha3.bytesAt m a 64=rppOf p σ)
    (hn : nonce=BitVec.ofNat 64 (p.ℓ*t+2*p.ℓ-1)) :
    commitTailSeed m a nonce=rppOf p σ++integerToBytes (p.ℓ*(t+1)+(p.ℓ-1)) 2 := by
  rw [commitTailSeed,hs,hn,nonceExtract_bytes (nextNonce_bound hp ht),nextNonce hp]

theorem nextPolynomial {p : Params} (hp : p=mlDsa65∨p=mlDsa87) {t : Nat} (ht : t<814)
    {m : Mem} {a : Addr} {σ : State} {nonce : BitVec 64}
    (hs : Spec.Sha3.bytesAt m a 64=rppOf p σ)
    (hn : nonce=BitVec.ofNat 64 (p.ℓ*t+2*p.ℓ-1)) :
    toRq (bitUnpack (H (commitTailSeed m a nonce) 640) 524287 524288)=
      Yv p σ (p.ℓ*(t+1)) (p.ℓ-1) := by
  rw [nextSeed hp ht hs hn]
  rcases hp with rfl|rfl <;> rfl

theorem nextPolynomial_of_phase {p : Params} (hp : p=mlDsa65∨p=mlDsa87)
    {S t i : Nat} {σ s : State} (h : PositiveICh p S σ t i s)
    (hn : s.gpr .x9=BitVec.ofNat 64 (p.ℓ*t+2*p.ℓ-1)) :
    toRq (bitUnpack (H (commitTailSeed s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc oMS)) (s.gpr .x9)) 640) 524287 524288)=
      Yv p σ (p.ℓ*(t+1)) (p.ℓ-1) :=
  nextPolynomial hp h.c.masks.l.t_lt h.c.masks.l.k.rpp hn

end VG.Proof.MlDsa.AArch64.Sign.Cached
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem hash_ok {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) {σ s : State} {t : Nat}
    (h : PositiveICh p S σ t p.k s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.hash p) s
      (fun u => PositiveIC p S σ t u ∧ Mask p σ (t+1) u) := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  unfold Impl.MlDsa.AArch64.Sign.Cached.hash
  refine WP.seq (WP.mono (hashSetup_ok hp3 h) fun a ⟨ha,hn,_⟩ => ?_)
  refine WP.mono (hashReady_phase hp hS ha) fun u ⟨hu,hm⟩ => ⟨hu,?_⟩
  rw [nextPolynomial_of_phase hp ha hn] at hm
  exact hm

theorem commit_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87) {σ s : State} {t : Nat}
    (h : PositiveIL p S σ t s) (hm : t=0 ∨ Mask p σ t s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.commit P p) s
      (fun u => PositiveIC p S σ t u ∧ Mask p σ (t+1) u) := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  unfold Impl.MlDsa.AArch64.Sign.Cached.commit
  refine WP.seq (WP.mono (masks_ok hP hp h hm) fun a ha => ?_)
  refine WP.seq (WP.mono (positiveRows_ok hp3 ha) fun b hb => ?_)
  refine WP.seq (WP.mono (positivePackRows_ok hP hp3 hb) fun c hc => ?_)
  exact hash_ok hp hP.s64 hc

end VG.Proof.MlDsa.AArch64.Sign.Cached
