import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Optimized
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCalls
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots

/-! ## From `OptimizedMask.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

/-- Check both slot permissions and preservation of the sampled mask. -/
def optimizedMaskChk (p : Params) (r : Nat) : Bool :=
  inB (sgR p++sgW p) (yhP p r) 1024 && inB (sgR p++sgW p) (yP p r) 1024 &&
  inB (sgW p) (yhP p r) 1024 && sepB (sgR p) (sgW p) (yhP p r) 1024 (yP p r) 1024 &&
  keepB (sgR p) (sgW p) [(yhP p r,1024)] (yP p r) 1024 &&
  stChk p [(yhP p r,1024)]

theorem optimizedMaskChk_ok {p : Params} (hp : Ok3 p) :
    ∀ r<p.ℓ,optimizedMaskChk p r=true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

/-- A direct-source transform keeps the original mask canonical, produces
its lazy NTT, and preserves the signing state and accumulated check flag. -/
theorem optimizedMaskFinish_ok {p : Params} {S : Nat} {σ s : State} {r : Nat} {f : Poly}
    (hc : optimizedMaskChk p r=true) (hs : St p S σ s)
    (ht : ForwardRoots s (pa s (yhP p r))) (hf : PolyIs s.mem (pa s (yP p r)) f) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.maskFinish p r) s fun t =>
      St p S σ t ∧ t.gpr .x24=s.gpr .x24 ∧
      PolyIs t.mem (pa t (yP p r)) f ∧
      PosPolyIs t.mem (pa t (yhP p r)) (ntt f) := by
  simp only [optimizedMaskChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨ho,hi⟩,hw⟩,hd⟩,hk⟩,hst⟩ := hc
  refine WP.mono (positiveNttOutAt_layout hs.lay ho hi hw hd ht hf.1)
    fun t ⟨hP,h24,hout⟩ => ?_
  refine ⟨hs.step hP hst,h24,hs.lay.keepPoly hP hk hf,?_⟩
  rw [hP.pa (hs.lay.ptrBs ho),hf.2] at *
  exact hout

/-- Preserve both static tables as well as the signing inputs across the
copy-free mask transform, ready for the next vector element. -/
theorem optimizedMaskFinish_rooted {p : Params} {S : Nat} {σ s : State} {r : Nat} {f : Poly}
    (hc : optimizedMaskChk p r=true) (hs : RootedSt p S σ s)
    (hf : PolyIs s.mem (pa s (yP p r)) f) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.maskFinish p r) s fun t =>
      RootedSt p S σ t ∧ t.gpr .x24=s.gpr .x24 ∧
      PolyIs t.mem (pa t (yP p r)) f ∧
      PosPolyIs t.mem (pa t (yhP p r)) (ntt f) := by
  simp only [optimizedMaskChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨ho,hi⟩,hw⟩,hd⟩,hk⟩,hst⟩ := hc
  have ht : ForwardRoots s (pa s (yhP p r)) :=
    ⟨hs.2.nttTableAt (hs.1.lay.inW hw),hs.2.forward.readable⟩
  refine WP.mono_syms (positiveNttOutAt_layout hs.1.lay ho hi hw hd ht hf.1)
    fun t ⟨hP,h24,hout⟩ hy => ?_
  refine ⟨hs.step hP hy hst (by simpa using hw),h24,hs.1.lay.keepPoly hP hk hf,?_⟩
  rw [hP.pa (hs.1.lay.ptrBs ho),hf.2] at *
  exact hout

theorem optimizedMaskReady {p : Params} {S : Nat} {σ s : State} {r : Nat}
    (hc : optimizedMaskChk p r=true) (hs : RootedSt p S σ s)
    (hf : Reduced s.mem (pa s (yP p r))) : NttOutCallReady (yhP p r) (yP p r) s := by
  simp only [optimizedMaskChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨ho,hi⟩,hw⟩,hd⟩,_⟩,_⟩ := hc
  exact ⟨hs.1.lay.nwp ho,hs.1.lay.nwp hi,hs.2.nttTableAt (hs.1.lay.inW hw),hf,
    hs.1.lay.disj hd,Covers.cons (hs.1.lay.cR hi)
      (Covers.cons hs.2.forward.readable (hs.1.lay.cR ho)),hs.1.lay.cW hw⟩

/-- The direct-source transform leaks no mask coefficient values. -/
theorem optimizedMaskFinish_tr {p : Params} {S : Nat} {r : Nat}
    (hc : optimizedMaskChk p r=true) {Q : State → State → Prop}
    (hQ : ∀ x y,Q x y →
      (∃ σ,RootedSt p S σ x) ∧ (∃ σ,RootedSt p S σ y) ∧
      Reduced x.mem (pa x (yP p r)) ∧ Reduced y.mem (pa y (yP p r)) ∧
      x.gpr .x28=y.gpr .x28 ∧ x.sp=y.sp ∧
      x.syms "VG_MLDSA_NTT_EXPANDED"=y.syms "VG_MLDSA_NTT_EXPANDED") :
    RelCT isa Q (Impl.MlDsa.AArch64.Sign.Optimized.maskFinish p r) fun _ _ => True := by
  apply positiveNttOutAt_tr (S := S) (ptr_ok (by change Reg.x28∈keptRegs; decide)) (ptr_ok (by change Reg.x28∈keptRegs; decide))
  intro x y hxy
  obtain ⟨⟨σx,hx⟩,⟨σy,hy⟩,rx,ry,h28,hsp,ht⟩ := hQ x y hxy
  exact ⟨optimizedMaskReady hc hx rx,optimizedMaskReady hc hy ry,
    by simp only [pa,h28],by simp only [pa,h28],hsp,ht⟩

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedMaskVector.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

/-- The transformed destination is apart from all sampled masks and from
the prefix of transforms already produced in the current attempt. -/
def optimizedMaskVectorChk (p : Params) (r : Nat) : Bool :=
  optimizedMaskChk p r &&
  famChk (sgR p) (sgW p) [(yhP p r,1024)] (5+p.k) (r+1) &&
  famChk (sgR p) (sgW p) [(yhP p r,1024)] (5+p.k+p.ℓ) r

theorem optimizedMaskVectorChk_ok {p : Params} (hp : Ok3 p) :
    ∀ r<p.ℓ,optimizedMaskVectorChk p r=true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

/-- One copy-free mask transform advances the positive vector invariant.
The canonical mask prefix is available to the later response calculation. -/
theorem optimizedMaskVector_step {p : Params} {S : Nat} {σ s : State} {r : Nat}
    {f : Nat → Poly} (hc : optimizedMaskVectorChk p r=true) (hs : RootedSt p S σ s)
    (hy : Fam s (5+p.k) (r+1) f)
    (hyt : PosFam s (5+p.k+p.ℓ) r (fun j => ntt (f j))) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.maskFinish p r) s fun t =>
      RootedSt p S σ t ∧ t.gpr .x24=s.gpr .x24 ∧
      Fam t (5+p.k) (r+1) f ∧ PosFam t (5+p.k+p.ℓ) (r+1) (fun j => ntt (f j)) := by
  simp only [optimizedMaskVectorChk,Bool.and_eq_true] at hc
  obtain ⟨⟨hm,hkeepy⟩,hkeept⟩ := hc
  simp only [optimizedMaskChk,Bool.and_eq_true] at hm
  obtain ⟨⟨⟨⟨⟨ho,hi⟩,hw⟩,hd⟩,_⟩,hst⟩ := hm
  have hf : PolyIs s.mem (pa s (yP p r)) (f r) := hy r (by omega)
  have ht : ForwardRoots s (pa s (yhP p r)) :=
    ⟨hs.2.nttTableAt (hs.1.lay.inW hw),hs.2.forward.readable⟩
  refine WP.mono_syms (positiveNttOutAt_layout hs.1.lay ho hi hw hd ht hf.1)
    fun t ⟨hP,h24,hout⟩ hsyms => ?_
  refine ⟨hs.step hP hsyms hst (by simpa using hw),h24,
    hy.keep hs.1.lay hP hkeepy,(hyt.keep hs.1.lay hP hkeept).snoc ?_⟩
  change PosPolyIs t.mem (pa t (yhP p r)) (ntt (f r))
  rw [hP.pa (hs.1.lay.ptrBs ho)]
  rw [hf.2] at hout
  exact hout

end VG.Proof.MlDsa.AArch64.Sign

end
