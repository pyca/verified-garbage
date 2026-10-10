import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterGroup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterRun

/-! ## From `InnerGroup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def innerBase (gap : Nat) : Reg := if gap=4 then .x3 else if gap=2 then .x4 else .x5

/-- The prearranged inner table is read-only through the arithmetic groups.
Roots may differ in each SIMD lane. -/
structure InnerRoots (s : State) (z : Nat → Nat → Nat → Int) : Prop where
  range : ∀ gap g, ValidGroup gap g → ∀ e < 4, 0 ≤ z gap g e ∧ z gap g e < 8380417
  q : ∀ e < 4, vword (s.v .v16) e = 8380417#32
  read : ∀ gap g, ValidGroup gap g → ∀ b ∈ [0,16],
    InRegions (s.rd++s.wr) (s.gpr (innerBase gap)+BitVec.ofNat 64 (32*g+b)) 16
  root : ∀ gap g, ValidGroup gap g → ∀ e < 4,
    vword (s.mem.read (s.gpr (innerBase gap)+BitVec.ofNat 64 (32*g)) 16) e =
      BitVec.ofInt 32 (z gap g e)
  reciprocal : ∀ gap g, ValidGroup gap g → ∀ e < 4,
    vword (s.mem.read (s.gpr (innerBase gap)+BitVec.ofNat 64 (32*g+16)) 16) e =
      BitVec.ofInt 32 (Optimized.reciprocal (z gap g e))

theorem InnerRoots.keep {s t : State} {z : Nat → Nat → Nat → Int} (h : InnerRoots s z)
    (hc : VChg outerRegs s t) : InnerRoots t z := by
  refine ⟨h.range, ?_, ?_, ?_, ?_⟩
  · intro e he
    rw [hc.get .v16 (by decide)]
    exact h.q e he
  · simpa only [hc.rd,hc.wr,hc.gpr] using h.read
  · simpa only [hc.mem,hc.gpr] using h.root
  · simpa only [hc.mem,hc.gpr] using h.reciprocal

theorem innerGroup_ok (r : Ren) (gap group : Nat) (hv : ValidGroup gap group)
    {s : State} {rest : List Instr} {Q : State → Prop} {values : Vector (BitVec 128) 8}
    {z : Nat → Nat → Nat → Int} (hr : GoodRen r) (hbank : Bank s r.data values)
    (hconst : InnerRoots s z)
    (k : ∀ t, VChg outerRegs s t → InnerRoots t z →
      Bank t (renGroup r gap group (rootAt (innerBase gap) group)).data
        (coreValues values gap group (z gap group)) → WP isa (.block rest) t Q) :
    WP isa (.block (rootAt (innerBase gap) group ++ coreCode r gap group ++ rest)) s Q := by
  have hg : group < 2048 := by
    rcases hv with ⟨rfl,rfl⟩ | ⟨rfl,hg⟩ | ⟨rfl,hg⟩ <;> omega
  rw [List.append_assoc]
  refine rootAt_ok (innerBase gap) group hg ?_ (hconst.read gap group hv 16 (by simp))
    fun s₁ hc₁ hz₁ hb₁ => ?_
  · simpa only [Nat.add_zero] using hconst.read gap group hv 0 (by simp)
  · have hp : ∀ v ∈ liveRegs, v ∉ prodTemps ∧ v ≠ VReg.v18 ∧ v ≠ VReg.v16 := by decide
    have hq₁ : ∀ e < 4, vword (s₁.v .v16) e = 8380417#32 := by
      intro e he
      rw [hc₁.get .v16]
      exact hconst.q e he
    refine coreCode_ok r gap group hv (hr.root_keep hbank hc₁) hr.injective hr.apart
      (fun i => (hp _ (hr.data i)).1) (fun i => (hp _ (hr.data i)).2.1)
      (fun i => (hp _ (hr.data i)).2.2) (hconst.range gap group hv) ?_ ?_ hq₁
      fun s₂ hc₂ h₂ _ _ => ?_
    · rw [hz₁]
      exact hconst.root gap group hv
    · rw [hb₁]
      exact hconst.reciprocal gap group hv
    · have hc : VChg outerRegs s s₂ := hc₁.trans (hc₂.mono (hr.coreClobs_mem gap group hv))
      refine k s₂ hc (hconst.keep hc) ?_
      rw [renGroup_data r gap group hv (rootAt (innerBase gap) group)]
      exact h₂

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `InnerRun.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def innerAfter (r : Ren) : List (Nat × Nat) → Ren
  | [] => r
  | (gap,g) :: ps => innerAfter (renGroup r gap g (rootAt (innerBase gap) g)) ps

def innerRun (r : Ren) : List (Nat × Nat) → List Instr
  | [] => []
  | (gap,g) :: ps => rootAt (innerBase gap) g ++ coreCode r gap g ++
      innerRun (renGroup r gap g (rootAt (innerBase gap) g)) ps

def innerValues (v : Vector (BitVec 128) 8) (z : Nat → Nat → Nat → Int) : List (Nat × Nat) → Vector (BitVec 128) 8
  | [] => v
  | (gap,g) :: ps => innerValues (coreValues v gap g (z gap g)) z ps

theorem innerAfter_code (r : Ren) (ps : List (Nat × Nat))
    (hv : ∀ p ∈ ps, ValidGroup p.1 p.2) :
    (innerAfter r ps).code = r.code ++ innerRun r ps := by
  induction ps generalizing r with
  | nil => simp only [innerAfter, innerRun, List.append_nil]
  | cons p ps ih =>
    rw [innerAfter, ih _ (fun p hp => hv p (List.mem_cons_of_mem _ hp)),
      renGroup_factor _ _ _ (hv p (by simp))]
    simp only [innerRun, List.append_assoc]

theorem innerRun_ok (r : Ren) (ps : List (Nat × Nat))
    (hv : ∀ p ∈ ps, ValidGroup p.1 p.2)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Vector (BitVec 128) 8}
    {z : Nat → Nat → Nat → Int} (hr : GoodRen r) (hbank : Bank s r.data v) (hconst : InnerRoots s z)
    (k : ∀ t, VChg outerRegs s t → InnerRoots t z →
      Bank t (innerAfter r ps).data (innerValues v z ps) → WP isa (.block rest) t Q) :
    WP isa (.block (innerRun r ps ++ rest)) s Q := by
  induction ps generalizing r s v with
  | nil => exact k s (VChg.refl _ _) hconst hbank
  | cons p ps ih =>
    have hvg := hv p (by simp)
    simp only [innerRun, List.append_assoc]
    have step := innerGroup_ok r p.1 p.2 hvg
      (rest := innerRun (renGroup r p.1 p.2 (rootAt (innerBase p.1) p.2)) ps ++ rest) (Q := Q)
      hr hbank hconst
    have run := step (fun s₁ hc₁ hconst₁ hbank₁ => by
      refine ih _ (fun p hp => hv p (List.mem_cons_of_mem _ hp)) (hr.group _ _ hvg _)
        hbank₁ hconst₁ fun s₂ hc₂ hconst₂ hbank₂ => ?_
      refine k s₂ (VChg.mono (hc₁.trans hc₂) ?_) hconst₂ hbank₂
      intro v hv
      simpa only [List.mem_append, or_self] using hv)
    simpa only [List.append_assoc] using run

theorem innerAfter_eq : innerAfter {} outerSteps = renThree false := by
  simp only [renThree, innerAfter, outerSteps, List.foldl_cons, List.foldl_nil,
    show List.range (4 / 4) = [0] from rfl,
    show List.range (4 / 2) = [0,1] from rfl,
    show List.range (4 / 1) = [0,1,2,3] from rfl, Bool.false_eq_true, ite_false, innerBase]

/-- The actual inner three fused register layers, before its surrounding loads/stores. -/
theorem innerThree_ok {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Vector (BitVec 128) 8} {z : Nat → Nat → Nat → Int}
    (hbank : Bank s ({} : Ren).data v) (hconst : InnerRoots s z)
    (k : ∀ t, VChg outerRegs s t → InnerRoots t z →
      Bank t (renThree false).data (innerValues v z outerSteps) → WP isa (.block rest) t Q) :
    WP isa (.block ((renThree false).code ++ rest)) s Q := by
  have he := innerAfter_code ({} : Ren) outerSteps outerSteps_valid
  rw [innerAfter_eq] at he
  change (renThree false).code = innerRun {} outerSteps at he
  rw [he]
  apply innerRun_ok {} outerSteps outerSteps_valid initial_good hbank hconst
  intro t hc ht hb
  rw [innerAfter_eq] at hb
  exact k t hc ht hb

end VG.Proof.MlDsa.AArch64.Optimized

end
