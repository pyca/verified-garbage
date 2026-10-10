import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedState
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCalls
import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Optimized

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Verify.Optimized
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.KeyGen (ifp ifn)

theorem nttZ_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {i : Nat} (hi : i<p.ℓ)
    (hs : SC p S σ h A' c0 q i false 0 s) :
    WP isa (forward (zP p i)) s (SC p S σ h A' c0 q (i+1) false 0) := by
  have L := hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hz := hs.z i hi
  simp only [Stored,decide_eq_false_iff_not.mpr (Nat.lt_irrefl i),Bool.false_eq_true,↓reduceIte,
    ifn (Nat.lt_irrefl i)] at hz
  have hr : inB (vR p++vW p) (zP p i) 1024=true := by vlayd
  have hw : inB (vW p) (zP p i) 1024=true := by vlayd
  refine WP.mono_syms (Sign.positiveNttAt_layout L hr hw
    ⟨hs.roots.nttTableAt (L.inW hw),hs.roots.forward.readable⟩ hz.1)
    fun t ⟨hP,x',hv⟩ hy=>?_
  refine ⟨hs.vc.step hF hp hP (by unfold vcChk;vlay),
    hs.roots.step_layout L hP hy (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact hw),
    hs.hh,L.keepHint hP (by vlayd) hs.hint,hs.nok,hs.gd,
    fun r' hr' c hc'=>L.keepPoly hP (by have := ar_lt hr' hc';vlay) (hs.a r' hr' c hc'),
    fun i' hi'=>?_,stored_keep L hP (by vlayd) hs.c,
    fun _ h=>absurd h (Nat.not_lt_zero _),x'.trans hs.x24⟩
  by_cases he : i'=i
  · subst i'
    simp only [Stored,decide_eq_true_eq.mpr (Nat.lt_succ_self i),↓reduceIte]
    rw [ifp (Nat.lt_succ_self i),hP.pa (show Reg.x28∈keptRegs by decide)]
    rw [hz.2] at hv
    exact hv
  · have hv' := stored_keep L hP (by vlayd) (hs.z i' hi')
    have hh : (i'<i+1)=(i'<i) := propext (by omega)
    simpa only [hh] using hv'

theorem nttC_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool}
    (hs : SC p S σ h A' c0 q p.ℓ false 0 s) :
    WP isa (forward (cP p)) s (SC p S σ h A' c0 q p.ℓ true 0) := by
  have L := hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hz : PolyIs s.mem (pa s (cP p)) c0 := hs.c
  have hr : inB (vR p++vW p) (cP p) 1024=true := by vlayd
  have hw : inB (vW p) (cP p) 1024=true := by vlayd
  refine WP.mono_syms (Sign.positiveNttAt_layout L hr hw
    ⟨hs.roots.nttTableAt (L.inW hw),hs.roots.forward.readable⟩ hz.1)
    fun t ⟨hP,x',hv⟩ hy=>?_
  refine ⟨hs.vc.step hF hp hP (by unfold vcChk;vlay),
    hs.roots.step_layout L hP hy (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact hw),
    hs.hh,L.keepHint hP (by vlayd) hs.hint,hs.nok,hs.gd,
    fun r' hr' c hc'=>L.keepPoly hP (by have := ar_lt hr' hc';vlay) (hs.a r' hr' c hc'),
    fun i hi=>stored_keep L hP (by vlayd) (hs.z i hi),?_,
    fun _ h=>absurd h (Nat.not_lt_zero _),x'.trans hs.x24⟩
  change PosPolyIs t.mem (pa t (cP p)) (ntt c0)
  rw [hP.pa (show Reg.x28∈keptRegs by decide)]
  rw [hz.2] at hv
  exact hv

end VG.Proof.MlDsa.AArch64.Verify.Optimized
