import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InnerGroup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterRun

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
