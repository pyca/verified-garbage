import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedMask

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
  rcases hp with rfl | rfl | rfl <;> decide

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
