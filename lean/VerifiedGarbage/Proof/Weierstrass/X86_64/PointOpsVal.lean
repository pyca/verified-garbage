import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsWrap
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafState
import VerifiedGarbage.Proof.Weierstrass.JacMul

/-!
# Point operations as functions on x86-64: what their bodies compute

The values the bodies of `Impl/Weierstrass/X86_64/PointOps.lean` leave in
`R`, as the formulas of `Spec/Weierstrass/PointOps.lean` of the values they
read, for any values: these are not the group law's facts (`InvJ`), which
the joint verifier's proofs use, but the field operations' results.
-/

namespace VG.Proof.Weierstrass.X86_64.PointOps

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

/-- `dblJMul` computes the specification's doubling. -/
theorem dblJMulN_spec {m : Nat} [NeZero m] (e : Nat → Fin m) :
    (runOps dblJMulN e 6, runOps dblJMulN e 7, runOps dblJMulN e 8) =
      Spec.Weierstrass.PointOps.jacDouble (e 11) (e 12) (e 13) := by
  dsimp only [dblJMulN, dblJMul, runOps, List.foldl, FOp.run, Function.update]
  rfl

/-- What the doubling's body keeps: `R`'s coordinates, distinct, are slots,
apart from `D`'s and the temporaries, which `dblJMul` writes and which are
slots too, and it reads only `R`. -/
structure DoubleLay (K : WinCfg) (size : Nat) (Sl : Nat → Prop) : Prop where
  lay : Lay K.M size Sl
  apart : RcbApart K.S K.R K.R K.D
  sl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.R, Sl x
  reads : readsOk (dblJMul K.S K.R K.D) (jacCoords K.R) = true
  accum : (jacCoords K.R).Nodup
  copy : ∀ x ∈ jacCoords K.D, ∀ y ∈ jacCoords K.R, x ≠ y

/-- The doubling's body: `R` becomes `jacDouble` of its values, and only
the temporaries, `D` and `R` change. -/
theorem doubleBody_val {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hD : DoubleLay K size Sl) (hm : UnitMod m (2 ^ (64 * K.M.n)))
    {E : Nat → Fin m} {s : State} (hI : Inv K.M base size m Sl (jacCoords K.R) E s) :
    WP isa (PointOps.doubleBody K).inline s fun t =>
      ProgKeep K.M base (rcbW K.S K.D ++ jacCoords K.R) s t ∧ ∃ E',
        Inv K.M base size m Sl (jacCoords K.R) E' t ∧
        (E' K.R.x, E' K.R.y, E' K.R.z) =
          Spec.Weierstrass.PointOps.jacDouble (E K.R.x) (E K.R.y) (E K.R.z) := by
  have he : dblJMul K.S K.R K.D = ofN dblJMulN K.S K.R K.R K.D := rfl
  have hN : NumOk dblJMulN := dblJChoiceN_ok true
  rw [PointOps.doubleBody]
  simp only [Code.inline]
  apply WP.seq
  refine WP.mono (fprogB_ok hD.lay hm _ hI (fun op hop x hx => hD.sl x (by
    rw [he] at hop; exact ofN_slots op hop x hx)) hD.reads) fun d ⟨kd, id⟩ => ?_
  have hDv : ∀ x ∈ jacCoords K.D, x ∈ validAfter (dblJMul K.S K.R K.D) (jacCoords K.R) := by
    intro x hx
    rw [mem_validAfter]
    right
    rw [he]
    exact ofN_out_mem hN (by simpa [jacCoords] using hx)
  have hRs : ∀ x ∈ jacCoords K.R, Sl x := fun x hx => hD.sl x (List.mem_append_right _ (by
    simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbR]))
  refine WP.mono (copyPointFields_ok hD.lay hD.accum hD.copy hRs id hDv)
    fun t ⟨E', kt, it, et⟩ => ⟨?_, E', it.sub fun x hx => List.mem_append_left _ hx, ?_⟩
  · refine (kd.mono fun w hw => ?_).trans (kt.mono fun w hw => List.mem_append_right _ hw)
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    rw [he] at hop
    exact List.mem_append_left _ (ofN_out hN op hop)
  · rw [et, he]
    have h6 := ofN_run hN hD.apart E 6
    have h7 := ofN_run hN hD.apart E 7
    have h8 := ofN_run hN hD.apart E 8
    have hs := dblJMulN_spec (fun y => E (rcbσ K.S K.R K.R K.D y))
    exact (congrArg₂ Prod.mk h6 (congrArg₂ Prod.mk h7 h8)).trans hs

end VG.Proof.Weierstrass.X86_64.PointOps
