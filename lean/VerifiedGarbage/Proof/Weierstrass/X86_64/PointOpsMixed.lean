import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsAdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedAdd
import VerifiedGarbage.Impl.Weierstrass.X86_64.JacMixedForward
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedForward

/-!
# Point operations as functions on x86-64: what the mixed addition computes

`addAffineBody`'s value: `R` becomes `jacAddAffine` of the values of `R`
and `E`, whatever they are, through the branches of
`Jacobian.jacMixedForward`: `E` copied for `R`'s `Z = 0`, else `R`'s `X`
and `Y` copied to `t2` and `t4`, the header's `H` and `r`, then the
doubling or the point at infinity for `H = 0`, else the tail.
-/

namespace VG.Proof.Weierstrass.X86_64.PointOps

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

theorem mixedN_spec {m : Nat} [NeZero m] (e : Nat → Fin m) :
    (runOps (jacMixedHeadN ++ jacMixedTailN) (jacMixedEnv e) 6,
      runOps (jacMixedHeadN ++ jacMixedTailN) (jacMixedEnv e) 7,
      runOps (jacMixedHeadN ++ jacMixedTailN) (jacMixedEnv e) 8) =
      Spec.Weierstrass.PointOps.jacTail (e 11) (e 12) (e 14 * (e 13 * e 13) - e 11)
        (e 15 * e 13 * (e 13 * e 13) - e 12) (e 13) := by
  simp only [jacMixedHeadN, jacMixedTailN, jacMixedHead, jacMixedTail, jacTail, jacMixedEnv,
    List.take, List.cons_append, List.nil_append, runOps, List.foldl_cons, List.foldl_nil, FOp.run,
    Function.update_apply]
  rfl

/-- What the mixed addition's body needs of the slots: those of
`Jacobian.jacMixedForward`'s proofs, and that its programs read only `R`
and `E` or what they wrote. -/
structure MixedLay (K : WinCfg) (size : Nat) (Sl : Nat → Prop) : Prop where
  lay : Lay K.M size Sl
  apart : RcbApart K.S K.R K.E K.D
  sl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.E, Sl x
  head : readsOk (jacMixedHead K.S K.R K.E) (K.S.t4 :: K.S.t2 :: (jacCoords K.R ++ jacCoords K.E)) = true
  tail : readsOk (jacMixedTail K.S K.R K.E K.D)
    (validAfter (jacMixedHead K.S K.R K.E) (K.S.t4 :: K.S.t2 :: (jacCoords K.R ++ jacCoords K.E))) = true
  dbl : readsOk (dblJMul K.S K.R K.D) (jacCoords K.R) = true
  accum : (jacCoords K.R).Nodup
  copy : ∀ x ∈ jacCoords K.D, ∀ y ∈ jacCoords K.R, x ≠ y
  dN : (jacCoords K.D).Nodup
  eD : ∀ x ∈ jacCoords K.E, ∀ y ∈ jacCoords K.D, x ≠ y

section
variable {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}

/-- The values the mixed addition reads. -/
abbrev mV (K : WinCfg) : List Nat := jacCoords K.R ++ jacCoords K.E

theorem mixedInit_val (hC : MixedLay K size Sl) {E : Nat → Fin m} {s : State}
    (hI : Inv K.M base size m Sl (mV K) E s) :
    WP isa (.block (copy K.M.n K.S.t2 K.R.x ++ copy K.M.n K.S.t4 K.R.y)) s fun t =>
      ProgKeep K.M base (rcbW K.S K.D) s t ∧
      Inv K.M base size m Sl (K.S.t4 :: K.S.t2 :: mV K) (jacMixedInit K.S K.R E) t := by
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok hC.lay hI (hC.sl K.S.t2 (by simp [rcbW])) (by simp [jacCoords]))
    fun a ⟨ka, ia⟩ => ?_
  refine WP.mono (copyField_ok hC.lay ia (hC.sl K.S.t4 (by simp [rcbW]))
    (List.mem_cons_of_mem _ (by simp [jacCoords]))) fun t ⟨kt, it⟩ =>
    ⟨(progKeep_of_op ka (by simp [rcbW])).trans (progKeep_of_op kt (by simp [rcbW])), it⟩

theorem mixedHead_val (hC : MixedLay K size Sl) (hm : UnitMod m (2 ^ (64 * K.M.n)))
    {E : Nat → Fin m} {s : State}
    (hI : Inv K.M base size m Sl (K.S.t4 :: K.S.t2 :: mV K) (jacMixedInit K.S K.R E) s) :
    WP isa (ForwardField.programB K.M (jacMixedHead K.S K.R K.E)).inline s fun t =>
      ProgKeep K.M base (rcbW K.S K.D) s t ∧
      Inv K.M base size m Sl (validAfter (jacMixedHead K.S K.R K.E) (K.S.t4 :: K.S.t2 :: mV K))
        (runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E)) t ∧
      runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E) K.S.t3 =
        E K.E.x * (E K.R.z * E K.R.z) - E K.R.x ∧
      runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E) K.S.t5 =
        E K.E.y * E K.R.z * (E K.R.z * E K.R.z) - E K.R.y := by
  rw [jacMixedHead_eq K.S K.R K.E K.D]
  have hr : readsOk (ofN jacMixedHeadN K.S K.R K.E K.D) (K.S.t4 :: K.S.t2 :: mV K) = true := hC.head
  refine WP.mono (ofN_forward_partial_ok hC.lay hm
    (show ∀ op ∈ jacMixedHeadN, op.out < 9 by decide) hC.apart hC.sl hI hr)
    fun t ⟨kt, it, he⟩ => ⟨kt, it, ?_, ?_⟩
  · have h := he 3
    rw [jacMixedInit_rename hC.apart] at h
    exact h.trans (jacMixedHeadN_run (fun i => E (rcbσ K.S K.R K.E K.D i))).1
  · have h := he 5
    rw [jacMixedInit_rename hC.apart] at h
    exact h.trans (jacMixedHeadN_run (fun i => E (rcbσ K.S K.R K.E K.D i))).2

theorem mixedTail_val (hC : MixedLay K size Sl) (hm : UnitMod m (2 ^ (64 * K.M.n)))
    {E : Nat → Fin m} {s : State}
    (hI : Inv K.M base size m Sl (validAfter (jacMixedHead K.S K.R K.E) (K.S.t4 :: K.S.t2 :: mV K))
      (runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E)) s) :
    WP isa (ForwardField.programB K.M (jacMixedTail K.S K.R K.E K.D)).inline s
      (Val K.M base size m Sl (rcbW K.S K.D) (mV K) K.D
        (Spec.Weierstrass.PointOps.jacTail (E K.R.x) (E K.R.y) (E K.E.x * (E K.R.z * E K.R.z) - E K.R.x)
          (E K.E.y * E K.R.z * (E K.R.z * E K.R.z) - E K.R.y) (E K.R.z)) s) := by
  let N := jacMixedHeadN ++ jacMixedTailN
  have he : jacMixedHead K.S K.R K.E ++ jacMixedTail K.S K.R K.E K.D = ofN N K.S K.R K.E K.D := by
    rw [jacMixedHead_eq K.S K.R K.E K.D, jacMixedTail_eq]
    simp only [N, ofN, List.map_append]
  have hN : ∀ op ∈ N, op.out < 9 := by decide
  have hw : ∀ op ∈ jacMixedTail K.S K.R K.E K.D, op.out ∈ rcbW K.S K.D := by
    intro op hop
    have hop' : op ∈ ofN N K.S K.R K.E K.D := he ▸ List.mem_append_right _ hop
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hop'
    rw [FOp.out_rename]
    exact rcbσ_out K.S K.R K.E K.D (hN n hn)
  have hv : ∀ x ∈ jacCoords K.D, x ∈ (jacMixedTail K.S K.R K.E K.D).map FOp.out := by
    intro x hx
    simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [jacMixedTail, jacTail, FOp.out]
  refine WP.mono (ForwardField.programB_ok hC.lay hm _ hI
    (fun op hop x hx => hC.sl x (ofN_slots op (he ▸ List.mem_append_right _ hop) x hx)) hC.tail)
    fun t ⟨kt, it⟩ => ⟨kt.mono ?_, runOps (jacMixedTail K.S K.R K.E K.D)
      (runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E)), ?_, ?_⟩
  · intro w hw'
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw'
    exact hw op hop
  · apply it.sub
    intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (hv x hx)
    · exact Or.inl ((mem_validAfter _ _).mpr (Or.inl (by simp [hx])))
  · rw [← runOps_append, he]
    have hren := runOps_rename (rcbσ K.S K.R K.E K.D) N (jacMixedInit K.S K.R E)
      (fun op hop => hC.apart.inj (hN op hop))
    rw [jacMixedInit_rename hC.apart] at hren
    exact (congrArg₂ Prod.mk (congrFun hren 6)
      (congrArg₂ Prod.mk (congrFun hren 7) (congrFun hren 8))).trans
      (mixedN_spec (fun i => E (rcbσ K.S K.R K.E K.D i)))

/-- `Jacobian.jacMixedForward` into `D`: `jacAddAffine` of the values it reads. -/
theorem mixedAdd_val (hC : MixedLay K size Sl) (hm : UnitMod m (2 ^ (64 * K.M.n)))
    (hOne : K.one < m) (hOneVal : toM m (2 ^ (64 * K.M.n)) K.one = 1)
    {E : Nat → Fin m} {s : State} (hI : Inv K.M base size m Sl (mV K) E s) :
    WP isa (Jacobian.jacMixedForward K K.R K.E K.D).inline s
      (Val K.M base size m Sl (rcbW K.S K.D) (mV K) K.D
        (Spec.Weierstrass.PointOps.jacAddAffine (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y)
          (E K.E.z)) s) := by
  have dW : ∀ w ∈ jacCoords K.D, w ∈ rcbW K.S K.D := by
    intro w hw; simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> simp [rcbW]
  have dSl : ∀ x ∈ jacCoords K.D, Sl x := fun x hx => hC.sl x (List.mem_append_left _ (dW x hx))
  have rV : ∀ x ∈ jacCoords K.R, x ∈ mV K := fun x hx => by simp [mV, hx]
  have eV : ∀ x ∈ jacCoords K.E, x ∈ mV K := fun x hx => by simp [mV, hx]
  rw [Jacobian.jacMixedForward]
  simp only [Code.inline]
  apply fieldBranch_ok hC.lay hm hI (rV _ (by simp [jacCoords]))
  · intro a ia ka hz
    refine WP.mono (copy_val hC.lay hC.dN hC.eD dSl ia eV) fun t ht => ?_
    simp only [Spec.Weierstrass.PointOps.jacAddAffine, hz, ↓reduceIte]
    exact (ht.mono dW).prefix ka (by simp)
  intro a ia ka hpz
  apply WP.seq
  refine WP.mono (mixedInit_val hC ia) fun b ⟨kb, ib⟩ => ?_
  apply WP.seq
  refine WP.mono (mixedHead_val hC hm ib) fun c ⟨kc, ic, eh, er⟩ => ?_
  have pre : ProgKeep K.M base (rcbW K.S K.D) s c := ((ka.mono (by simp)).trans kb).trans kc
  let EH := runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E)
  have hro : ∀ x ∈ jacCoords K.R, EH x = E x := fun x hx =>
    jacMixedHead_readonly hC.apart E (by
      simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [rcbR])
  have oldV : ∀ x ∈ mV K, x ∈ validAfter (jacMixedHead K.S K.R K.E) (K.S.t4 :: K.S.t2 :: mV K) :=
    fun x hx => (mem_validAfter _ _).mpr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
  apply fieldBranch_ok hC.lay hm ic (a := K.S.t3) (by
    rw [mem_validAfter]; right; simp [jacMixedHead, FOp.out])
  · intro d id kd hH
    apply fieldBranch_ok hC.lay hm id (a := K.S.t5) (by
      rw [mem_validAfter]; right; simp [jacMixedHead, FOp.out])
    · intro e ie ke hr
      have hdA : RcbApart K.S K.R K.R K.D :=
        ⟨hC.apart.nodup, fun x hx => hC.apart.apart x (rcbR_self_mem _ _ _ hx)⟩
      have hdSl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.R, Sl x := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hC.sl x (List.mem_append_left _ hx)
        · exact hC.sl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
      have hR' := readsOk_mono hC.dbl fun x hx => oldV x (rV x hx)
      refine WP.mono (dblB_val hC.lay hm hdA hdSl hR' ie) fun t ht => ?_
      have hs : Spec.Weierstrass.PointOps.jacAddAffine (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y)
          (E K.E.z) = Spec.Weierstrass.PointOps.jacDouble (EH K.R.x) (EH K.R.y) (EH K.R.z) := by
        rw [eh] at hH
        rw [er] at hr
        rw [hro _ (by simp [jacCoords]), hro _ (by simp [jacCoords]), hro _ (by simp [jacCoords])]
        simp only [Spec.Weierstrass.PointOps.jacAddAffine, Spec.Weierstrass.PointOps.jacEqual, hpz,
          ↓reduceIte]
        simp only [hH, hr, ↓reduceIte]
      rw [hs]
      exact (((ht.sub oldV).prefix ke (by simp)).prefix kd (by simp)).prefix pre (fun _ h => h)
    · intro e ie ke hr
      refine WP.mono (infinity_val hC.lay dSl dW hC.dN ie hOne hOneVal) fun t ht => ?_
      have hs : Spec.Weierstrass.PointOps.jacAddAffine (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y)
          (E K.E.z) = (0, 1, 0) := by
        rw [eh] at hH
        rw [er] at hr
        simp only [Spec.Weierstrass.PointOps.jacAddAffine, Spec.Weierstrass.PointOps.jacEqual,
          Spec.Weierstrass.PointOps.infinity, hpz, ↓reduceIte]
        simp only [hH, hr, ↓reduceIte]
      rw [hs]
      exact (((ht.sub oldV).prefix ke (by simp)).prefix kd (by simp)).prefix pre (fun _ h => h)
  · intro d id kd hH
    refine WP.mono (mixedTail_val hC hm id) fun t ht => ?_
    have hs : Spec.Weierstrass.PointOps.jacAddAffine (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y)
        (E K.E.z) = Spec.Weierstrass.PointOps.jacTail (E K.R.x) (E K.R.y)
          (E K.E.x * (E K.R.z * E K.R.z) - E K.R.x) (E K.E.y * E K.R.z * (E K.R.z * E K.R.z) - E K.R.y)
          (E K.R.z) := by
      rw [eh] at hH
      simp only [Spec.Weierstrass.PointOps.jacAddAffine, hpz, hH, ↓reduceIte]
    rw [hs]
    exact (ht.prefix kd (by simp)).prefix pre (fun _ h => h)

/-- The mixed addition's body: `R` becomes `jacAddAffine` of what it reads. -/
theorem addAffineBody_val (hC : MixedLay K size Sl) (hm : UnitMod m (2 ^ (64 * K.M.n)))
    (hOne : K.one < m) (hOneVal : toM m (2 ^ (64 * K.M.n)) K.one = 1)
    {E : Nat → Fin m} {s : State} (hI : Inv K.M base size m Sl (mV K) E s) :
    WP isa (PointOps.addAffineBody K).inline s fun t =>
      ProgKeep K.M base (rcbW K.S K.D ++ jacCoords K.R) s t ∧ ∃ E',
        Inv K.M base size m Sl (jacCoords K.R) E' t ∧ (E' K.R.x, E' K.R.y, E' K.R.z) =
          Spec.Weierstrass.PointOps.jacAddAffine (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y)
            (E K.E.z) := by
  rw [PointOps.addAffineBody]
  simp only [Code.inline]
  apply WP.seq
  refine WP.mono (mixedAdd_val hC hm hOne hOneVal hI) fun d ⟨kd, E', id, ed⟩ => ?_
  have rSl : ∀ x ∈ jacCoords K.R, Sl x := fun x hx => hC.sl x (List.mem_append_right _ (by
      simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [rcbR]))
  refine WP.mono (copyPointFields_ok hC.lay hC.accum hC.copy rSl id (fun x hx => List.mem_append_left _ hx))
    fun t ⟨E'', kt, it, et⟩ => ⟨(kd.mono fun w hw => List.mem_append_left _ hw).trans
      (kt.mono fun w hw => List.mem_append_right _ hw), E'', it.sub fun x hx => List.mem_append_left _ hx,
      et.trans ed⟩

end
end VG.Proof.Weierstrass.X86_64.PointOps
