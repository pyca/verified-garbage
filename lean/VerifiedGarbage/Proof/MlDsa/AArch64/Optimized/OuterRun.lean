import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterGroup

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
  · omega

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
