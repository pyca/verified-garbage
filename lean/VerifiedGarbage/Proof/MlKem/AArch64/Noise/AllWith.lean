module

public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyPair
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlKem.AArch64.Lay

/-! # Accumulating all paired noise outputs -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem (PolyIsW)
open VG.Proof.MlKem (cw)
open VG.Spec.MlKem

theorem all_loop_okWith {s : State} {L : KemLay} (nttAt : Nat→Nat→Prog isa) (kg : Bool) (hk : 0<L.k)
    (rs : List Region) (out : Nat → Addr) (value : Nat → Poly) (writes : Nat → List Region)
    (hsub : ∀i<L.k, ∀r∈writes i, r∈rs)
    (hfar : ∀i<L.k, ∀j<2*i, ∀r∈writes i, (polyRegion (out j)).Disjoint r)
    (hstep : ∀i<L.k, ∀t, Kept rs s t → t.syms=s.syms →
      WP isa (Impl.MlKem.AArch64.Noise.noisePairWith nttAt L kg (2*i)) t fun u =>
        Kept (writes i) t u ∧ PolyIsW (cw true) u.mem (out (2*i)) (value (2*i)) ∧
        PolyIsW (cw true) u.mem (out (2*i+1)) (value (2*i+1))) :
    WP isa (Impl.MlKem.AArch64.Noise.noiseAllWith nttAt L kg) s fun t =>
      Kept rs s t ∧ ∀j<2*L.k, PolyIsW (cw true) t.mem (out j) (value j) := by
  apply WP.mono (Q:=fun t : State=> (Kept rs s t ∧ t.syms=s.syms) ∧ ∀j<2*L.k, PolyIsW (cw true) t.mem (out j) (value j)) ?_ (fun _ h=>⟨h.1.1,h.2⟩)
  apply WPs.seqs (map_range_ne_nil hk _)
  apply WPs.range (I := fun i t => (Kept rs s t ∧ t.syms=s.syms) ∧ ∀j<2*i, PolyIsW (cw true) t.mem (out j) (value j))
  · intro i hi t ⟨⟨kt,st⟩,old⟩
    refine WP.mono_syms (hstep i hi t kt st) fun u ⟨ku,a,b⟩ ut => ?_
    refine ⟨⟨kt.trans (ku.mono (hsub i hi)),ut.trans st⟩,fun j hj => ?_⟩
    by_cases hj0 : j<2*i
    · exact Proof.MlKem.polyIsW_frame_poly ku.frame (hfar i hi j hj0) (old j hj0)
    · rcases (show j=2*i ∨ j=2*i+1 by omega) with rfl | rfl
      · exact a
      · exact b
  · exact ⟨⟨Kept.refl rs s,rfl⟩,fun j hj => by omega⟩

end VG.Proof.MlKem.AArch64.Noise
