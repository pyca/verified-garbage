module
public import VerifiedGarbage.Impl.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.Jac


/-! The direct-product doubling schedule permits its input and output to coincide. -/

@[expose] public section

namespace VG.Proof.Weierstrass
open VG.Impl.Weierstrass

/-- The schedule in place on numbered slots: the temporaries at `0 … 5`, the point at `6 … 8`. -/
private def dblJMulN : List FOp := dblJMul ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨6, 7, 8⟩ ⟨6, 7, 8⟩

/-- On numbered slots the reads through the writes are decided, and what is left is the identity. -/
private theorem dblJMulN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps dblJMulN e 6, runOps dblJMulN e 7, runOps dblJMulN e 8) = dblJF (e 6) (e 7) (e 8) := by
  dsimp only [dblJMulN, dblJMul, runOps, List.foldl, FOp.run, Function.update]
  simp only [dblJF, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- Slot `i` of `dblJMulN` as a slot of `dblJMul S p p`: one that is not written, from `9` on. -/
private def inσ (S : RcbSlots) (p : Pt) (i : Nat) : Nat := (rcbW S p ++ []).getD i ((rcbW S p).sum + 1)

private theorem le_sum : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ l.sum
  | a :: l, x, h => by
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (le_sum l x h) (Nat.le_add_left _ _)

theorem dblJMul_inplace_run {F : Type _} [Lean.Grind.CommRing F]
    {S : RcbSlots} {p : Pt} (h : (rcbW S p).Nodup) (e : Nat → F) :
    (runOps (dblJMul S p p) e p.x,runOps (dblJMul S p p) e p.y,
      runOps (dblJMul S p p) e p.z)=dblJF (e p.x) (e p.y) (e p.z) := by
  -- The slots are the numbered ones renamed (`runOps_rename`): with the slots variables, each `grind`
  -- decided the reads through the twenty writes again.
  have hd : (rcbW S p).sum + 1 ∉ rcbW S p := fun hm => Nat.not_succ_le_self _ (le_sum _ _ hm)
  have key := runOps_rename (inσ S p) dblJMulN e fun op hop y hy =>
    getD_append_inj h (fun _ hx => absurd hx List.not_mem_nil) hd
      ((by decide : ∀ op ∈ dblJMulN, op.out < 9) op hop) y hy
  have r := dblJMulN_run fun y => e (inσ S p y)
  rw [← congrFun key 6, ← congrFun key 7, ← congrFun key 8] at r
  rw [show dblJMul S p p = dblJMulN.map (FOp.rename (inσ S p)) from rfl,
    show p.x = inσ S p 6 from rfl, show p.y = inσ S p 7 from rfl, show p.z = inσ S p 8 from rfl]
  exact r

end VG.Proof.Weierstrass
