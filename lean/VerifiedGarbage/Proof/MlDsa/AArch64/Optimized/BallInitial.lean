import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFirst
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallZero
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSponge
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Ball

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.Sha3 (bytesAt stateAt)
open VG.Proof.MlDsa.AArch64.Sample.Ball (spOf W St)

abbrev firstBytes (σ : State) := Spec.MlDsa.H ((spOf σ).msg σ) 136
abbrev tailBytes (σ : State) := Spec.Sha3.squeezeFrom 136
  (padded 136 Spec.Sha3.shakeSuffix ((spOf σ).msg σ)) 136 136

structure Initial (σ s : State) : Prop where
  env : Env (spOf σ) σ s
  parser : Parser (spOf σ).a (ballFold (tauOf σ) (firstBytes σ)).1
    (ballFold (tauOf σ) (firstBytes σ)).2
    (W (firstBytes σ) >>> ((ballFold (tauOf σ) (firstBytes σ)).2-(256-tauOf σ))) s
  pos : (s.gpr .x0).toNat≤136
  next : Spec.Sha3.squeezeFrom 136 (stateAt s.mem (spOf σ).scr) (s.gpr .x0).toNat 136=tailBytes σ

 theorem initial_full_ok {σ s : State} (hp : sbK.pre σ) (h : Resume 136 136 (spOf σ) σ s) :
    WP isa (.seq Impl.MlDsa.AArch64.Optimized.Ball.zeroWide Impl.MlDsa.AArch64.Optimized.Ball.first)
      s (fun u => Initial σ u ∧ u.gpr .x0=s.gpr .x0) := by
  have ps := Sample.Ball.spOk hp
  have hl : (firstBytes σ).length=136 := H_length _ _
  refine WP.seq (WP.mono (zeroWide_coeffs h.first.env.x26 (fun i hi => ?_)) fun t ⟨kt,ft,hz⟩ => ?_)
  · rw [h.first.env.wr,ps.wr]
    exact in_regions (List.mem_cons_self ..) (Offset.contains_base _ (by omega) (by omega))
  have et := h.first.env.keepA ps kt ft
  have ot : bytesAt t.mem ((spOf σ).at' 840) 136=firstBytes σ := by
    rw [MlKem.bytesAt_frame ft (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (a_scr' ps (by decide)).symm) (by decide),h.first.out]
    exact (H_eq _ _).symm
  have st : stateAt t.mem (spOf σ).scr=stateAt s.mem (spOf σ).scr :=
    state_frame ft (fun r hr => by rw [List.mem_singleton.mp hr]; exact ps.a_scr.symm.sub_left (sub_scr0 (by decide)))
  refine WP.mono (first_ok (τ := tauOf σ) (b := (spOf σ).at' 840) hl (by rw [et.x25]) et.x26
    (by rw [et.x27]; simp [tauOf]; omega) (by have := (Sample.Ball.params hp).2.2; omega)
    (inScrRd ps et.rd et.wr (by decide))
    (fun j hj => by rw [at_add]; exact inScrRd ps et.rd et.wr (by omega))
    (fun j hj => by rw [← ot,MlKem.bytesAt_getD _ _ hj])
    (fun j hj => inA ps et.wr hj) (a_scr' ps (by decide)).symm hz) fun u hu => ?_
  have eqfold : St (firstBytes σ) (tauOf σ) 128=ballFold (tauOf σ) (firstBytes σ) := by
    simp only [St,ballFold]
    rw [List.take_of_length_le (by rw [List.length_drop,hl])]
  refine ⟨⟨et.keepA ps hu.keep hu.frame,?_,?_,?_⟩,by rw [hu.keep.get .x0,kt.get .x0]⟩
  · simpa only [eqfold] using hu.parser
  · rw [hu.keep.get .x0,kt.get .x0]; exact h.pos
  · have su : stateAt u.mem (spOf σ).scr=stateAt t.mem (spOf σ).scr :=
      state_frame hu.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact ps.a_scr.symm.sub_left (sub_scr0 (by decide)))
    rw [su,st,hu.keep.get .x0,kt.get .x0]
    exact h.next 136
theorem initial_ok {σ s : State} (hp : sbK.pre σ) (h : Resume 136 136 (spOf σ) σ s) :
    WP isa (.seq Impl.MlDsa.AArch64.Optimized.Ball.zeroWide Impl.MlDsa.AArch64.Optimized.Ball.first)
      s (Initial σ) := WP.mono (initial_full_ok hp h) fun _ hh => hh.1
end VG.Proof.MlDsa.AArch64.Optimized.Ball
