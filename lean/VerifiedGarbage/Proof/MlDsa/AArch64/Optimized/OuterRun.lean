module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Registers
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Table

/-! ### `MlDsa.AArch64.Optimized.OuterGroup`, which only this module used -/

section

/-! ## From `Hoisted.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def outerRegs : List VReg := [.v18,.v19] ++ groupRegs

/-- The four loaded vectors hold eight interleaved roots and exact reciprocals. -/
structure Hoisted (s : State) (z : Nat → Int) : Prop where
  range : ∀ i < 8, 0 ≤ z (i+1) ∧ z (i+1) < 8380417
  q : ∀ e < 4, vword (s.v .v16) e = 8380417#32
  roots : ∀ g < 4, ∀ e < 4, vword (s.v rootRegs[g]!) e =
    if e % 2 = 0 then BitVec.ofInt 32 (z (2*g+e/2+1))
    else BitVec.ofInt 32 (reciprocal (z (2*g+e/2+1)))

theorem Hoisted.keep {s t : State} {z : Nat → Int} (h : Hoisted s z)
    (hc : VChg outerRegs s t) : Hoisted t z := by
  refine ⟨h.range, ?_, ?_⟩
  · intro e he
    rw [hc.get .v16 (by decide)]
    exact h.q e he
  · intro g hg e he
    have hn : ∀ i : Fin 4, rootRegs[i.val]! ∉ outerRegs := by decide
    rw [hc.get _ (hn ⟨g,hg⟩)]
    exact h.roots g hg e he

theorem GoodRen.root_keep {r : Ren} {s t : State} {values : Vector (BitVec 128) 8}
    (hr : GoodRen r) (h : Bank s r.data values) (hc : VChg [.v18,.v19] s t) :
    Bank t r.data values := by
  intro i
  have hn : ∀ v ∈ liveRegs, v ∉ [VReg.v18,.v19] := by decide
  rw [hc.get _ (hn _ (hr.data i))]
  exact h i

/-- Extract a chosen outer-layer root without modifying the hoisted constants. -/
theorem hoistedRoot_ok (index : Nat) (hi : 1 ≤ index) (hi' : index ≤ 8)
    {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (h : Hoisted s z)
    (k : ∀ t, VChg [.v18,.v19] s t →
      (∀ e < 4, vword (t.v .v18) e = BitVec.ofInt 32 (z index)) →
      (∀ e < 4, vword (t.v .v19) e = BitVec.ofInt 32 (reciprocal (z index))) →
      WP isa (.block rest) t Q) :
    WP isa (.block (hoistedRoot index ++ rest)) s Q := by
  have hg : (index-1)/2 < 4 := by omega_using [hi']
  have hp : (index-1)%2 < 2 := by omega_using []
  have hs : ∀ g : Fin 4, rootRegs[g.val]! ≠ .v18 := by decide
  refine rootPair_ok rootRegs[(index-1)/2]! ((index-1)%2) hp (hs ⟨_,hg⟩) fun t hc ha hb => ?_
  refine k t hc ?_ ?_
  · intro e he
    rw [ha e he, h.roots _ hg _ (by omega_using [])]
    have hm : (2*((index-1)%2))%2 = 0 := by omega_using []
    have heq : 2*((index-1)/2)+(2*((index-1)%2))/2+1 = index := by omega_using [hi]
    rw [hm, ite_eq_left rfl, heq]
  · intro e he
    rw [hb e he, h.roots _ hg _ (by omega_using [])]
    have hm : ¬ (2*((index-1)%2)+1)%2 = 0 := by omega_using []
    have heq : 2*((index-1)/2)+(2*((index-1)%2)+1)/2+1 = index := by omega_using [hi]
    rw [ite_eq_right hm, heq]

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `OuterGroup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem outerGroup_ok (r : Ren) (gap group index : Nat) (hv : ValidGroup gap group)
    (hi : 1 ≤ index) (hi' : index ≤ 8)
    {s : State} {rest : List Instr} {Q : State → Prop} {values : Vector (BitVec 128) 8}
    {z : Nat → Int} (hr : GoodRen r) (hbank : Bank s r.data values) (hconst : Hoisted s z)
    (k : ∀ t, VChg outerRegs s t → Hoisted t z →
      Bank t (renGroup r gap group (hoistedRoot index)).data
        (coreValues values gap group (fun _ => z index)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (hoistedRoot index ++ coreCode r gap group ++ rest)) s Q := by
  rw [List.append_assoc]
  refine hoistedRoot_ok index hi hi' hconst fun s₁ hc₁ hz₁ hb₁ => ?_
  have hrange : 0 ≤ z index ∧ z index < 8380417 := by
    have h := hconst.range (index-1) (by omega_using [hi'])
    rwa [Nat.sub_add_cancel hi] at h
  have hp : ∀ v ∈ liveRegs, v ∉ prodTemps ∧ v ≠ VReg.v18 ∧ v ≠ VReg.v16 := by decide
  have hq₁ : ∀ e < 4, vword (s₁.v .v16) e = 8380417#32 := by
    intro e he
    rw [hc₁.get .v16]
    exact hconst.q e he
  refine coreCode_ok r gap group hv (hr.root_keep hbank hc₁) hr.injective hr.apart
    (fun i => (hp _ (hr.data i)).1) (fun i => (hp _ (hr.data i)).2.1)
    (fun i => (hp _ (hr.data i)).2.2) (fun _ _ => hrange) hz₁ hb₁ hq₁
    fun s₂ hc₂ h₂ _ _ => ?_
  have hc : VChg outerRegs s s₂ := hc₁.trans (hc₂.mono (hr.coreClobs_mem gap group hv))
  refine k s₂ hc (hconst.keep hc) ?_
  rw [renGroup_data r gap group hv (hoistedRoot index)]
  exact h₂

end VG.Proof.MlDsa.AArch64.Optimized

end

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def outerSteps : List (Nat × Nat) := [(4,0),(2,0),(2,1),(1,0),(1,1),(1,2),(1,3)]

def outerAfter (r : Ren) : List (Nat × Nat) → Ren
  | [] => r
  | (gap,g) :: ps => outerAfter (renGroup r gap g (hoistedRoot (4/gap+g))) ps

def outerRun (r : Ren) : List (Nat × Nat) → List Instr
  | [] => []
  | (gap,g) :: ps => hoistedRoot (4/gap+g) ++ coreCode r gap g ++
      outerRun (renGroup r gap g (hoistedRoot (4/gap+g))) ps

def outerValues (v : Vector (BitVec 128) 8) (z : Nat → Int) : List (Nat × Nat) → Vector (BitVec 128) 8
  | [] => v
  | (gap,g) :: ps => outerValues (coreValues v gap g (fun _ => z (4/gap+g))) z ps

theorem ValidGroup.root_index {gap g : Nat} (h : ValidGroup gap g) :
    1 ≤ 4/gap+g ∧ 4/gap+g ≤ 8 := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,hg⟩ | ⟨rfl,hg⟩
  · decide
  · rcases hg with rfl | rfl <;> decide
  · omega_using [hg]

theorem outerAfter_code (r : Ren) (ps : List (Nat × Nat))
    (hv : ∀ p ∈ ps, ValidGroup p.1 p.2) :
    (outerAfter r ps).code = r.code ++ outerRun r ps := by
  induction ps generalizing r with
  | nil => simp only [outerAfter, outerRun, List.append_nil]
  | cons p ps ih =>
    rw [outerAfter, ih _ (fun p hp => hv p (List.mem_cons_of_mem _ hp)),
      renGroup_factor _ _ _ (hv p (by simp))]
    simp only [outerRun, List.append_assoc]

theorem outerRun_ok (r : Ren) (ps : List (Nat × Nat))
    (hv : ∀ p ∈ ps, ValidGroup p.1 p.2)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Vector (BitVec 128) 8}
    {z : Nat → Int} (hr : GoodRen r) (hbank : Bank s r.data v) (hconst : Hoisted s z)
    (k : ∀ t, VChg outerRegs s t → Hoisted t z →
      Bank t (outerAfter r ps).data (outerValues v z ps) → WP isa (.block rest) t Q) :
    WP isa (.block (outerRun r ps ++ rest)) s Q := by
  induction ps generalizing r s v with
  | nil => exact k s (VChg.refl _ _) hconst hbank
  | cons p ps ih =>
    have hvg := hv p (by simp)
    have hb := hvg.root_index
    simp only [outerRun, List.append_assoc]
    have step := outerGroup_ok r p.1 p.2 (4/p.1+p.2) hvg hb.1 hb.2
      (rest := outerRun (renGroup r p.1 p.2 (hoistedRoot (4/p.1+p.2))) ps ++ rest) (Q := Q)
      hr hbank hconst
    have run := step (fun s₁ hc₁ hconst₁ hbank₁ => by
      refine ih _ (fun p hp => hv p (List.mem_cons_of_mem _ hp)) (hr.group _ _ hvg _)
        hbank₁ hconst₁ fun s₂ hc₂ hconst₂ hbank₂ => ?_
      refine k s₂ (VChg.mono (hc₁.trans hc₂) ?_) hconst₂ hbank₂
      intro v hv
      simpa only [List.mem_append, or_self] using hv)
    simpa only [List.append_assoc] using run

theorem outerSteps_valid : ∀ p ∈ outerSteps, ValidGroup p.1 p.2 := by
  simp only [outerSteps, List.mem_cons, List.not_mem_nil, or_false]
  intro p hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ValidGroup]

theorem outerAfter_eq : outerAfter {} outerSteps = renThree true := by
  simp only [renThree, outerAfter, outerSteps, List.foldl_cons, List.foldl_nil,
    show List.range (4 / 4) = [0] from rfl,
    show List.range (4 / 2) = [0,1] from rfl,
    show List.range (4 / 1) = [0,1,2,3] from rfl, ite_true]

/-- The actual first three fused layers, before its surrounding loads/stores. -/
theorem outerThree_ok {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Vector (BitVec 128) 8} {z : Nat → Int}
    (hbank : Bank s ({} : Ren).data v) (hconst : Hoisted s z)
    (k : ∀ t, VChg outerRegs s t → Hoisted t z →
      Bank t (renThree true).data (outerValues v z outerSteps) → WP isa (.block rest) t Q) :
    WP isa (.block ((renThree true).code ++ rest)) s Q := by
  have he := outerAfter_code ({} : Ren) outerSteps outerSteps_valid
  rw [outerAfter_eq] at he
  change (renThree true).code = outerRun {} outerSteps at he
  rw [he]
  apply outerRun_ok {} outerSteps outerSteps_valid initial_good hbank hconst
  intro t hc ht hb
  rw [outerAfter_eq] at hb
  exact k t hc ht hb

end VG.Proof.MlDsa.AArch64.Optimized
