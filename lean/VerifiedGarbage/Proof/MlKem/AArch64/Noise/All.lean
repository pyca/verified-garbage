module

public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.Impl.MlKem.AArch64.Noise
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

/-! # Accumulating all paired noise outputs -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem

theorem all_loop_ok {s : State} {L : KemLay} (kg : Bool) (hk : 0<L.k)
    (rs : List Region) (out : Nat → Addr) (value : Nat → Poly) (writes : Nat → List Region)
    (hsub : ∀i<L.k, ∀r∈writes i, r∈rs)
    (hfar : ∀i<L.k, ∀j<2*i, ∀r∈writes i, (polyRegion (out j)).Disjoint r)
    (hstep : ∀i<L.k, ∀t, Kept rs s t →
      WP isa (Impl.MlKem.AArch64.Noise.noisePair L kg (2*i)) t fun u =>
        Kept (writes i) t u ∧ PolyIs u.mem (out (2*i)) (value (2*i)) ∧
        PolyIs u.mem (out (2*i+1)) (value (2*i+1))) :
    WP isa (Impl.MlKem.AArch64.Noise.noiseAll L kg) s fun t =>
      Kept rs s t ∧ ∀j<2*L.k, PolyIs t.mem (out j) (value j) := by
  apply WPs.seqs (map_range_ne_nil hk _)
  apply WPs.range (I := fun i t => Kept rs s t ∧ ∀j<2*i, PolyIs t.mem (out j) (value j))
  · intro i hi t ⟨kt,old⟩
    refine WP.mono (hstep i hi t kt) fun u ⟨ku,a,b⟩ => ?_
    refine ⟨kt.trans (ku.mono (hsub i hi)),fun j hj => ?_⟩
    by_cases hj0 : j<2*i
    · exact Proof.MlKem.polyIs_frame ku.frame (hfar i hi j hj0) (old j hj0)
    · rcases (show j=2*i ∨ j=2*i+1 by omega) with rfl | rfl
      · exact a
      · exact b
  · exact ⟨Kept.refl rs s,fun j hj => by omega⟩

end VG.Proof.MlKem.AArch64.Noise
