import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsMixed
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedTiming

/-!
# Point operations as functions on x86-64: the additions' timing

The Jacobian additions branch on the values they read: two runs from states
whose slots `V` hold the same values `E` (`FieldPair`) leak the same trace,
as `cachedJacAdd_relCT` and `jacMixedForward_relCT` show for the joint
verifier, here for any values (`CachedLay`, `MixedLay`: the programs read
only `V` or what they wrote), with the pieces' taint checks
(`CachedJacChecks`, `JacMixedChecks`).
-/

namespace VG.Proof.Weierstrass.X86_64.PointOps

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

/-- A program `ops` reading `V` or what it wrote, constant time if its code is. -/
theorem programB_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {ops : List FOp}
    (hS : ∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) {V : List Nat} (hR : readsOk ops V = true)
    {E : Nat → Fin m} (hc : ScratchCT (ForwardField.programB M ops).inline) :
    RelCT isa (FieldPair M base size m Sl V E) (ForwardField.programB M ops).inline
      (FieldPair M base size m Sl (validAfter ops V) (runOps ops E)) :=
  fieldProgram_relCT hc fun _ hi => WP.mono (ForwardField.programB_ok hL hm _ hi hS hR) fun _ ht => ht.2

theorem validAfter_sub {ops : List FOp} {V : List Nat} {o : Pt}
    (ho : ∀ x ∈ jacCoords o, x ∈ ops.map FOp.out) :
    ∀ x ∈ jacCoords o ++ V, x ∈ validAfter ops V := by
  intro x hx
  rw [mem_validAfter]
  rcases List.mem_append.mp hx with hx | hx
  · exact Or.inr (ho x hx)
  · exact Or.inl hx

section
variable {K : WinCfg} {sel : Nat} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}

theorem cachedAdd_relCT (hC : CachedPts (m := m) K sel size Sl) (hm : UnitMod m (2 ^ (64 * K.M.n)))
    (hc : CachedJacChecks K K.R K.E K.D sel) {E : Nat → Fin m} :
    RelCT isa (FieldPair K.M base size m Sl (cV K sel) E)
      (Impl.Weierstrass.X86_64.CachedJac.add K K.R K.E K.D sel).inline
      (fun s t => ∃ E', FieldPair K.M base size m Sl (jacCoords K.D ++ cV K sel) E' s t) := by
  have hL := hC.lay
  have dW : ∀ w ∈ jacCoords K.D, w ∈ rcbW K.S K.D := by
    intro w hw; simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> simp [rcbW]
  have dSl : ∀ x ∈ jacCoords K.D, Sl x := fun x hx => hL.sl x (List.mem_append_left _
    (List.mem_append_left _ (dW x hx)))
  have rV : ∀ x ∈ jacCoords K.R, x ∈ cV K sel := fun x hx => by simp [cV, hx]
  have eV : ∀ x ∈ jacCoords K.E, x ∈ cV K sel := fun x hx => by simp [cV, hx]
  rw [Impl.Weierstrass.X86_64.CachedJac.add]
  apply fieldBranch_relCT hL.lay hm (rV _ (by simp [jacCoords])) hc.zeroP
  · intro _
    exact (copyPoint_relCT hL.lay dSl eV hc.copyQ).mono (fun _ _ h => h) (fun _ _ h => ⟨_, h⟩)
  intro _
  apply fieldBranch_relCT hL.lay hm (eV _ (by simp [jacCoords])) hc.zeroQ
  · intro _
    exact (copyPoint_relCT hL.lay dSl rV hc.copyP).mono (fun _ _ h => h) (fun _ _ h => ⟨_, h⟩)
  intro _
  apply RelCT.seq (fieldProgram_relCT hc.head (fun s hi =>
    WP.mono (cachedHead_val hL hm hi) (fun _ ht => ht.2.1)))
  have oldV : ∀ x ∈ cV K sel, x ∈ validAfter (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel) (cV K sel) :=
    fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
  have subV : ∀ x ∈ jacCoords K.D ++ cV K sel, x ∈ jacCoords K.D ++
      validAfter (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel) (cV K sel) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (oldV x hx)
  apply fieldBranch_relCT hL.lay hm (a := K.S.t3) (by
    rw [mem_validAfter]; right; simp [Impl.Weierstrass.X86_64.CachedJac.head, FOp.out]) hc.zeroH
  · intro _
    apply fieldBranch_relCT hL.lay hm (a := K.S.t5) (by
      rw [mem_validAfter]; right; simp [Impl.Weierstrass.X86_64.CachedJac.head, FOp.out]) hc.zeroR
    · intro _
      have he : dblJMul K.S K.R K.D = ofN dblJMulN K.S K.R K.R K.D := rfl
      have hN : NumOk dblJMulN := dblJChoiceN_ok true
      refine (programB_relCT hL.lay hm (fun op hop x hx => hL.sl x (by
          rw [he] at hop
          rcases List.mem_append.mp (ofN_slots op hop x hx) with h | h
          · exact List.mem_append_left _ (List.mem_append_left _ h)
          · exact List.mem_append_left _ (List.mem_append_right _ (rcbR_self_mem _ _ _ h))))
        (readsOk_mono hL.dbl fun x hx => oldV x (rV x hx)) hc.double).mono (fun _ _ h => h)
        (fun _ _ h => ⟨_, (h.sub (validAfter_sub fun x hx => by
          rw [he]; exact ofN_out_mem hN (by simpa [jacCoords] using hx))).sub subV⟩)
    · intro _
      exact (infinity_relCT hL.lay dSl hC.one hc.infinity).mono
        (fun _ _ h => h) (fun _ _ h => ⟨_, h.sub subV⟩)
  · intro _
    refine (programB_relCT hL.lay hm (fun op hop x hx => hL.sl x (by
        rw [CachedJac.tail_eq K.M.n K.S K.R K.E K.D sel] at hop
        exact CachedJac.slots op hop x hx)) hL.tail hc.tail).mono (fun _ _ h => h)
      (fun _ _ h => ⟨_, (h.sub (validAfter_sub fun x hx => by
        simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> simp [jacTail, FOp.out])).sub subV⟩)

/-- The cached addition's body, its sum copied to `R`. -/
theorem addCachedBody_relCT (hC : CachedPts (m := m) K sel size Sl) (hm : UnitMod m (2 ^ (64 * K.M.n)))
    (hc : CachedJacChecks K K.R K.E K.D sel) (hcp : ScratchCT (.block (copyPt K.M.n K.R K.D)))
    {E : Nat → Fin m} :
    RelCT isa (FieldPair K.M base size m Sl (cV K sel) E) (PointOps.addCachedBody K sel).inline
      (fun s t => ∃ E', FieldPair K.M base size m Sl (jacCoords K.R) E' s t) := by
  rw [PointOps.addCachedBody]
  apply RelCT.seq (cachedAdd_relCT hC hm hc)
  apply RelCT.exists_
  intro E'
  have rSl : ∀ x ∈ jacCoords K.R, Sl x := fun x hx => hC.lay.sl x (List.mem_append_left _
    (List.mem_append_right _ (by
      simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [rcbR])))
  exact (copyPoint_relCT (E := E') hC.lay.lay rSl (fun x hx => List.mem_append_left _ hx) hcp).mono
    (fun _ _ h => h) (fun _ _ h => ⟨_, h.sub fun x hx => List.mem_append_left _ hx⟩)

end

section
variable {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}

theorem mixedAdd_relCT (hC : MixedLay K size Sl) (hm : UnitMod m (2 ^ (64 * K.M.n))) (hOne : K.one < m)
    (hc : JacMixedChecks K K.R K.E K.D) {E : Nat → Fin m} :
    RelCT isa (FieldPair K.M base size m Sl (mV K) E) (Jacobian.jacMixedForward K K.R K.E K.D).inline
      (fun s t => ∃ E', FieldPair K.M base size m Sl (jacCoords K.D ++ mV K) E' s t) := by
  have dW : ∀ w ∈ jacCoords K.D, w ∈ rcbW K.S K.D := by
    intro w hw; simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> simp [rcbW]
  have dSl : ∀ x ∈ jacCoords K.D, Sl x := fun x hx => hC.sl x (List.mem_append_left _ (dW x hx))
  have rV : ∀ x ∈ jacCoords K.R, x ∈ mV K := fun x hx => by simp [mV, hx]
  have eV : ∀ x ∈ jacCoords K.E, x ∈ mV K := fun x hx => by simp [mV, hx]
  rw [Jacobian.jacMixedForward]
  apply fieldBranch_relCT hC.lay hm (rV _ (by simp [jacCoords])) hc.zeroP
  · intro _
    exact (copyPoint_relCT hC.lay dSl eV hc.copyQ).mono (fun _ _ h => h) (fun _ _ h => ⟨_, h⟩)
  intro _
  apply RelCT.seq (fieldProgram_relCT hc.init (fun s hi =>
    WP.mono (mixedInit_val hC hi) (fun _ ht => ht.2)))
  apply RelCT.seq (fieldProgram_relCT hc.head (fun s hi =>
    WP.mono (mixedHead_val hC hm hi) (fun _ ht => ht.2.1)))
  have oldV : ∀ x ∈ mV K, x ∈ validAfter (jacMixedHead K.S K.R K.E) (K.S.t4 :: K.S.t2 :: mV K) :=
    fun x hx => (mem_validAfter _ _).mpr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
  have subV : ∀ x ∈ jacCoords K.D ++ mV K, x ∈ jacCoords K.D ++
      validAfter (jacMixedHead K.S K.R K.E) (K.S.t4 :: K.S.t2 :: mV K) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (oldV x hx)
  apply fieldBranch_relCT hC.lay hm (a := K.S.t3) (by
    rw [mem_validAfter]; right; simp [jacMixedHead, FOp.out]) hc.zeroH
  · intro _
    apply fieldBranch_relCT hC.lay hm (a := K.S.t5) (by
      rw [mem_validAfter]; right; simp [jacMixedHead, FOp.out]) hc.zeroR
    · intro _
      have he : dblJMul K.S K.R K.D = ofN dblJMulN K.S K.R K.R K.D := rfl
      have hN : NumOk dblJMulN := dblJChoiceN_ok true
      refine (programB_relCT hC.lay hm (fun op hop x hx => hC.sl x (by
          rw [he] at hop
          rcases List.mem_append.mp (ofN_slots op hop x hx) with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (rcbR_self_mem _ _ _ h)))
        (readsOk_mono hC.dbl fun x hx => oldV x (rV x hx)) hc.double).mono (fun _ _ h => h)
        (fun _ _ h => ⟨_, (h.sub (validAfter_sub fun x hx => by
          rw [he]; exact ofN_out_mem hN (by simpa [jacCoords] using hx))).sub subV⟩)
    · intro _
      exact (infinity_relCT hC.lay dSl hOne hc.infinity).mono
        (fun _ _ h => h) (fun _ _ h => ⟨_, h.sub subV⟩)
  · intro _
    have he : jacMixedTail K.S K.R K.E K.D = ofN jacMixedTailN K.S K.R K.E K.D := rfl
    refine (programB_relCT hC.lay hm (fun op hop x hx => hC.sl x (by
        rw [he] at hop
        exact ofN_slots op hop x hx)) hC.tail hc.tail).mono (fun _ _ h => h)
      (fun _ _ h => ⟨_, (h.sub (validAfter_sub fun x hx => by
        simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> simp [jacMixedTail, jacTail, FOp.out])).sub subV⟩)

/-- The mixed addition's body, its sum copied to `R`. -/
theorem addAffineBody_relCT (hC : MixedLay K size Sl) (hm : UnitMod m (2 ^ (64 * K.M.n))) (hOne : K.one < m)
    (hc : JacMixedChecks K K.R K.E K.D) (hcp : ScratchCT (.block (copyPt K.M.n K.R K.D)))
    {E : Nat → Fin m} :
    RelCT isa (FieldPair K.M base size m Sl (mV K) E) (PointOps.addAffineBody K).inline
      (fun s t => ∃ E', FieldPair K.M base size m Sl (jacCoords K.R) E' s t) := by
  rw [PointOps.addAffineBody]
  apply RelCT.seq (mixedAdd_relCT hC hm hOne hc)
  apply RelCT.exists_
  intro E'
  have rSl : ∀ x ∈ jacCoords K.R, Sl x := fun x hx => hC.sl x (List.mem_append_right _ (by
      simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [rcbR]))
  exact (copyPoint_relCT (E := E') hC.lay rSl (fun x hx => List.mem_append_left _ hx) hcp).mono
    (fun _ _ h => h) (fun _ _ h => ⟨_, h.sub fun x hx => List.mem_append_left _ hx⟩)

end

end VG.Proof.Weierstrass.X86_64.PointOps
