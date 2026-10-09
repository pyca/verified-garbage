import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedCopy
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedMasks

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
