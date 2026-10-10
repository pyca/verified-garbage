import VerifiedGarbage.Proof.P384.X86_64.PointOpsLay
import VerifiedGarbage.Proof.P384.X86_64.PointOpsLit
import VerifiedGarbage.Proof.P384.X86_64.JointTiming
import VerifiedGarbage.Proof.P384.X86_64.JacTiming
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# P-384's point functions on x86-64: their `Verified`

The facts of `Spec.Weierstrass.PointOps.p384`'s contracts on x86-64 (`ws`
in `rdi`, `fnPre`), which the functions meet (`fn_ok` and the bodies'
values): the spec's coordinates are the slots' field elements (`pt_eq`,
given Fermat's little theorem in `Fin p`, from the curve's group law).
The additions, whose branches depend on the points, are constant time by
relating two runs from states whose points agree (`FieldPair`).
-/

namespace VG.Proof.P384.X86_64.PointOps

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.P384.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Weierstrass.X86_64.PointOps
open VG.Impl.P384.X86_64.PointOps (addCachedFn addAffineFn)

/-- P-384's curve of `Spec/Weierstrass/PointOps.lean`. -/
abbrev C : Spec.Weierstrass.PointOps.Curve := Spec.Weierstrass.PointOps.p384

/-- The spec's point at `o` is the slots' field elements. -/
theorem pt_eq (hFe : Point.Fermat C.p) (m : Mem) (ws : Addr) {o : Nat} (ho : o + 16 * 6 < 2 ^ 32) :
    C.pt ws m o = (env C.p 6 m ws o, env C.p 6 m ws (o + 8 * 6), env C.p 6 m ws (o + 16 * 6)) := by
  have dq := Point.dec_eq C.toCurve (by decide +kernel) hFe (unitMod_pow_two p_odd _)
  have hk : C.k = 6 := rfl
  simp only [Spec.Weierstrass.PointOps.Curve.pt, Spec.Weierstrass.Point.Curve.decPt,
    Spec.Weierstrass.Point.Curve.pointAt, Spec.Weierstrass.Point.elemBytes, dq, env, Spec.Weierstrass.Point.Curve.R, hk]
  rw [coordAt_eq _ _ _ (by omega), coordAt_eq _ _ _ (by omega), coordAt_eq _ _ _ (by omega), hk,
    show 2 * (8 * 6) = 16 * 6 from rfl]

/-- What every function's analysis may consider public, but for the additions'
points. -/
def fnPub (s₁ s₂ : State) : Prop := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi

theorem below_lt {m : Mem} {ws : Addr} {o : Nat} (ho : o + 16 * 6 < 2 ^ 32)
    (h : C.Below (C.pointAt m ws o)) :
    wordsVal m ws o 6 < C.p ∧ wordsVal m ws (o + 8 * 6) 6 < C.p ∧ wordsVal m ws (o + 16 * 6) 6 < C.p := by
  obtain ⟨h0, h1, h2⟩ := h
  have hk : C.k = 6 := rfl
  simp only [Spec.Weierstrass.Point.Curve.pointAt, Spec.Weierstrass.Point.elemBytes, hk] at h0 h1 h2
  rw [coordAt_eq _ _ _ (by omega), hk] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem el_eq (hFe : Point.Fermat C.p) (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) :
    C.el ws m o = env C.p 6 m ws o := by
  have dq := Point.dec_eq C.toCurve (by decide +kernel) hFe (unitMod_pow_two p_odd _)
  have hk : C.k = 6 := rfl
  simp only [Spec.Weierstrass.PointOps.Curve.el, dq, env, Spec.Weierstrass.Point.Curve.R, hk]
  rw [coordAt_eq _ _ _ ho, hk]

/-- The cached addition's contract on x86-64. -/
def addCachedK : Contract isa where
  pre s := fnPre s ∧ C.ModOk (s.gpr .rdi) s.mem ∧ C.Below (C.pointAt s.mem (s.gpr .rdi) C.pAt) ∧
    C.Below (C.pointAt s.mem (s.gpr .rdi) C.qAt) ∧ C.CoordBelow (s.gpr .rdi) s.mem C.zzAt ∧
    C.CoordBelow (s.gpr .rdi) s.mem C.zzzAt
  post s s' := let P := C.pt (s.gpr .rdi) s.mem C.pAt
    let Q := C.pt (s.gpr .rdi) s.mem C.qAt
    C.Result C.pAt (Spec.Weierstrass.PointOps.jacAddCached P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2
      (C.el (s.gpr .rdi) s.mem C.zzAt) (C.el (s.gpr .rdi) s.mem C.zzzAt)) (s.gpr .rdi) s.mem s'.mem
  pub s₁ s₂ := fnPub s₁ s₂ ∧ C.reads true (s₁.gpr .rdi) s₁.mem = C.reads true (s₂.gpr .rdi) s₂.mem

/-- The mixed addition's contract on x86-64. -/
def addAffineK : Contract isa where
  pre s := fnPre s ∧ C.ModOk (s.gpr .rdi) s.mem ∧ C.Below (C.pointAt s.mem (s.gpr .rdi) C.pAt) ∧
    C.Below (C.pointAt s.mem (s.gpr .rdi) C.qAt)
  post s s' := let P := C.pt (s.gpr .rdi) s.mem C.pAt
    let Q := C.pt (s.gpr .rdi) s.mem C.qAt
    C.Result C.pAt (Spec.Weierstrass.PointOps.jacAddAffine P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2)
      (s.gpr .rdi) s.mem s'.mem
  pub s₁ s₂ := fnPub s₁ s₂ ∧ C.reads false (s₁.gpr .rdi) s₁.mem = C.reads false (s₂.gpr .rdi) s₂.mem

theorem rV (adx : Bool) : ∀ x ∈ jacCoords (K adx).R, Sl adx x := fun x hx =>
  (doubleLay adx).sl x (List.mem_append_right _ (by
    simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbR]))

theorem eV (adx : Bool) : ∀ x ∈ jacCoords (K adx).E, Sl adx x := fun x hx =>
  (cachedPts adx).lay.sl x (List.mem_append_left _ (List.mem_append_right _ (by
    simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbR])))

theorem addCached_correct (hFe : Point.Fermat C.p) (adx : Bool)
    (hok : wrapOk (addCachedFn adx) = true) (s : State) (hs : addCachedK.pre s) :
    ∃ t s', Exec isa (addCachedFn adx) s t s' ∧ abiPreserved s s' ∧ addCachedK.post s s' := by
  obtain ⟨hp, hmod, hbp, hbq, h2, h3⟩ := hs
  have lp := below_lt (by decide) hbp
  have lq := below_lt (by decide) hbq
  have hsel : sel + 8 * (K adx).M.n = C.zzzAt := by rw [K_n]; rfl
  obtain ⟨t, s', he, ha, hB, hv, hK⟩ := fn_ok (fnCfg adx)
    (body := Impl.Weierstrass.X86_64.PointOps.addCachedBody (K adx) sel)
    (V := cV (K adx) sel)
    (r := fun E => Spec.Weierstrass.PointOps.jacAddCached (E (K adx).R.x) (E (K adx).R.y) (E (K adx).R.z)
      (E (K adx).E.x) (E (K adx).E.y) (E (K adx).E.z) (E sel) (E (sel + 8 * (K adx).M.n)))
    hok (by cases adx <;> decide +kernel) (fun x hx => by
      simp only [cV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (hx | hx) | rfl | rfl
      · exact rV adx x hx
      · exact eV adx x hx
      · exact (cachedPts adx).lay.sl _ (by simp)
      · exact (cachedPts adx).lay.sl _ (by simp))
    (fun s E hI => WP.mono (addCachedBody_val (cachedPts adx) (unitMod_pow_two p_odd _) hI)
      fun t ⟨kt, E', it, et⟩ => ⟨kt, E', it, et⟩) s hp hmod (by
      intro x hx
      rw [K_n]
      simp only [cV, jacCoords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      have c2 := h2
      have c3 := h3
      simp only [Spec.Weierstrass.PointOps.Curve.CoordBelow] at c2 c3
      rw [coordAt_eq _ _ _ (by decide)] at c2 c3
      rcases hx with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl | rfl
      · exact (fnCfg adx).rx ▸ lp.1
      · exact (fnCfg adx).ry ▸ lp.2.1
      · exact (fnCfg adx).rz ▸ lp.2.2
      · exact (fnCfg adx).ex ▸ lq.1
      · exact (fnCfg adx).ey ▸ lq.2.1
      · exact (fnCfg adx).ez ▸ lq.2.2
      · exact c2
      · rw [hsel]; exact c3)
  refine ⟨t, s', he, ha, hB, ?_, hK⟩
  rw [pt_eq hFe _ _ (by decide), pt_eq hFe _ _ (by decide), pt_eq hFe _ _ (by decide),
    el_eq hFe _ _ (by decide), el_eq hFe _ _ (by decide)]
  rw [show C.k = 6 from rfl] at hv
  rw [hv, (fnCfg adx).rx, (fnCfg adx).ry, (fnCfg adx).rz, (fnCfg adx).ex, (fnCfg adx).ey,
    (fnCfg adx).ez, hsel, K_n]
  rfl

theorem addAffine_correct (hFe : Point.Fermat C.p) (adx : Bool)
    (hok : wrapOk (addAffineFn adx) = true) (s : State) (hs : addAffineK.pre s) :
    ∃ t s', Exec isa (addAffineFn adx) s t s' ∧ abiPreserved s s' ∧ addAffineK.post s s' := by
  obtain ⟨hp, hmod, hbp, hbq⟩ := hs
  have lp := below_lt (by decide) hbp
  have lq := below_lt (by decide) hbq
  obtain ⟨t, s', he, ha, hB, hv, hK⟩ := fn_ok (fnCfg adx)
    (body := Impl.Weierstrass.X86_64.PointOps.addAffineBody (K adx))
    (V := mV (K adx))
    (r := fun E => Spec.Weierstrass.PointOps.jacAddAffine (E (K adx).R.x) (E (K adx).R.y) (E (K adx).R.z)
      (E (K adx).E.x) (E (K adx).E.y) (E (K adx).E.z))
    hok (by cases adx <;> decide +kernel) (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact rV adx x hx
      · exact eV adx x hx)
    (fun s E hI => WP.mono (addAffineBody_val (mixedLay adx) (unitMod_pow_two p_odd _) (one_lt adx)
      (one_val adx) hI) fun t ⟨kt, E', it, et⟩ => ⟨kt, E', it, et⟩) s hp hmod (by
      intro x hx
      rw [K_n]
      simp only [mV, jacCoords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | rfl | rfl) | (rfl | rfl | rfl)
      · exact (fnCfg adx).rx ▸ lp.1
      · exact (fnCfg adx).ry ▸ lp.2.1
      · exact (fnCfg adx).rz ▸ lp.2.2
      · exact (fnCfg adx).ex ▸ lq.1
      · exact (fnCfg adx).ey ▸ lq.2.1
      · exact (fnCfg adx).ez ▸ lq.2.2)
  refine ⟨t, s', he, ha, hB, ?_, hK⟩
  rw [pt_eq hFe _ _ (by decide), pt_eq hFe _ _ (by decide), pt_eq hFe _ _ (by decide)]
  rw [show C.k = 6 from rfl] at hv
  rw [hv, (fnCfg adx).rx, (fnCfg adx).ry, (fnCfg adx).rz, (fnCfg adx).ex, (fnCfg adx).ey,
    (fnCfg adx).ez, K_n]
  rfl

/-! ## Constant time -/

theorem cachedChecks : ∀ adx, CachedJacChecks (K adx) (K adx).R (K adx).E (K adx).D sel
  | false => nafCachedJac_checks
  | true => nafCachedJac_adx_checks

theorem mixedChecks : ∀ adx, JacMixedChecks (K adx) (K adx).R (K adx).E (K adx).D
  | false => nafMixedJac_checks
  | true => nafMixedJac_adx_checks

theorem copyCt : ∀ adx, ScratchCT (.block (copyPt (K adx).M.n (K adx).R (K adx).D))
  | false => joint_cached_checks.copy
  | true => joint_adx_cached_checks.copy

theorem bytes_length (ws : Addr) (m : Mem) (o n : Nat) :
    (Spec.Weierstrass.PointOps.Curve.bytes ws m o n).length = n := by
  simp [Spec.Weierstrass.PointOps.Curve.bytes]

/-- The offsets of the numbers the additions read. -/
def readSlots (cached : Bool) : List Nat :=
  [736, 784, 832, 1024, 1072, 1120] ++ if cached then [6160, 6208] else []

/-- Runs from states whose points' (and cached powers') bytes agree read the
same numbers. -/
theorem reads_wordsVal {cached : Bool} {ws : Addr} {m₁ m₂ : Mem}
    (h : C.reads cached ws m₁ = C.reads cached ws m₂) {x : Nat} (hx : x ∈ readSlots cached) :
    wordsVal m₁ ws x 6 = wordsVal m₂ ws x 6 := by
  simp only [Spec.Weierstrass.PointOps.Curve.reads, List.append_assoc] at h
  obtain ⟨hp, h'⟩ := append_bytes h (by rw [bytes_length, bytes_length])
  obtain ⟨hq, hc⟩ := append_bytes h' (by rw [bytes_length, bytes_length])
  simp only [readSlots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) | hx
  · exact wordsVal_of_bytes hp (by decide) (by decide)
  · exact wordsVal_of_bytes hp (by decide) (by decide)
  · exact wordsVal_of_bytes hp (by decide) (by decide)
  · exact wordsVal_of_bytes hq (by decide) (by decide)
  · exact wordsVal_of_bytes hq (by decide) (by decide)
  · exact wordsVal_of_bytes hq (by decide) (by decide)
  · cases cached
    · simp at hx
    · simp only [↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact wordsVal_of_bytes hc (by decide) (by decide)
      · exact wordsVal_of_bytes hc (by decide) (by decide)

theorem cV_readSlots (adx : Bool) : ∀ x ∈ cV (K adx) sel, x ∈ readSlots true := by
  cases adx <;> decide +kernel

theorem mV_readSlots (adx : Bool) : ∀ x ∈ mV (K adx), x ∈ readSlots false := by
  cases adx <;> decide +kernel

theorem addCached_ct (adx : Bool) : ConstantTime isa addCachedK.pre addCachedK.pub (addCachedFn adx) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ hp e₁ e₂
  obtain ⟨⟨_, hrdi⟩, hr⟩ := hp
  rw [← hrdi] at hr
  have lt (s : State) (hs : addCachedK.pre s) : ∀ x ∈ cV (K adx) sel, wordsVal s.mem (s.gpr .rdi) x (K adx).M.n < C.p := by
    obtain ⟨_, _, hbp, hbq, h2, h3⟩ := hs
    have lp := below_lt (by decide) hbp
    have lq := below_lt (by decide) hbq
    simp only [Spec.Weierstrass.PointOps.Curve.CoordBelow] at h2 h3
    rw [coordAt_eq _ _ _ (by decide)] at h2 h3
    intro x hx
    rw [K_n]
    simp only [cV, jacCoords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl | rfl
    · exact (fnCfg adx).rx ▸ lp.1
    · exact (fnCfg adx).ry ▸ lp.2.1
    · exact (fnCfg adx).rz ▸ lp.2.2
    · exact (fnCfg adx).ex ▸ lq.1
    · exact (fnCfg adx).ey ▸ lq.2.1
    · exact (fnCfg adx).ez ▸ lq.2.2
    · exact h2
    · rw [K_n]; exact h3
  have hV : ∀ x ∈ cV (K adx) sel, Sl adx x := fun x hx => by
    simp only [cV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (hx | hx) | rfl | rfl
    · exact rV adx x hx
    · exact eV adx x hx
    · exact (cachedPts adx).lay.sl _ (by simp)
    · exact (cachedPts adx).lay.sl _ (by simp)
  have I₁ := inv_of (fnCfg adx) hV p₁.1 p₁.2.1 (lt s₁ p₁)
  have I₂ := inv_of (fnCfg adx) hV p₂.1 p₂.2.1 (lt s₂ p₂)
  rw [← hrdi] at I₂
  have ag : ∀ x ∈ cV (K adx) sel, env C.p (K adx).M.n s₂.mem (s₁.gpr .rdi) x =
      env C.p (K adx).M.n s₁.mem (s₁.gpr .rdi) x := by
    intro x hx
    simp only [env, K_n]
    rw [reads_wordsVal hr.symm (cV_readSlots adx x hx)]
  have hb := addCachedBody_relCT (base := s₁.gpr .rdi) (cachedPts adx) (unitMod_pow_two p_odd _)
    (cachedChecks adx) (copyCt adx) (E := env C.p (K adx).M.n s₁.mem (s₁.gpr .rdi))
  rw [Code.inline_of_noCalls (by cases adx <;> decide +kernel)] at hb
  exact (wrap_relCT hb s₁ s₂ t₁ t₂ s₁' s₂' ⟨I₁, I₂.congr_env ag⟩ e₁ e₂).1

theorem addAffine_ct (adx : Bool) : ConstantTime isa addAffineK.pre addAffineK.pub (addAffineFn adx) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ hp e₁ e₂
  obtain ⟨⟨_, hrdi⟩, hr⟩ := hp
  rw [← hrdi] at hr
  have lt (s : State) (hs : addAffineK.pre s) : ∀ x ∈ mV (K adx), wordsVal s.mem (s.gpr .rdi) x (K adx).M.n < C.p := by
    obtain ⟨_, _, hbp, hbq⟩ := hs
    have lp := below_lt (by decide) hbp
    have lq := below_lt (by decide) hbq
    intro x hx
    rw [K_n]
    simp only [mV, jacCoords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl) | (rfl | rfl | rfl)
    · exact (fnCfg adx).rx ▸ lp.1
    · exact (fnCfg adx).ry ▸ lp.2.1
    · exact (fnCfg adx).rz ▸ lp.2.2
    · exact (fnCfg adx).ex ▸ lq.1
    · exact (fnCfg adx).ey ▸ lq.2.1
    · exact (fnCfg adx).ez ▸ lq.2.2
  have hV : ∀ x ∈ mV (K adx), Sl adx x := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact rV adx x hx
    · exact eV adx x hx
  have I₁ := inv_of (fnCfg adx) hV p₁.1 p₁.2.1 (lt s₁ p₁)
  have I₂ := inv_of (fnCfg adx) hV p₂.1 p₂.2.1 (lt s₂ p₂)
  rw [← hrdi] at I₂
  have ag : ∀ x ∈ mV (K adx), env C.p (K adx).M.n s₂.mem (s₁.gpr .rdi) x =
      env C.p (K adx).M.n s₁.mem (s₁.gpr .rdi) x := by
    intro x hx
    simp only [env, K_n]
    rw [reads_wordsVal (cached := false) hr.symm (mV_readSlots adx x hx)]
  have hb := addAffineBody_relCT (base := s₁.gpr .rdi) (mixedLay adx) (unitMod_pow_two p_odd _)
    (one_lt adx) (mixedChecks adx) (copyCt adx) (E := env C.p (K adx).M.n s₁.mem (s₁.gpr .rdi))
  rw [Code.inline_of_noCalls (by cases adx <;> decide +kernel)] at hb
  exact (wrap_relCT hb s₁ s₂ t₁ t₂ s₁' s₂' ⟨I₁, I₂.congr_env ag⟩ e₁ e₂).1

end VG.Proof.P384.X86_64.PointOps
