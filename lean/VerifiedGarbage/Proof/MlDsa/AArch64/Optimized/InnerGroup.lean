import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterGroup

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
