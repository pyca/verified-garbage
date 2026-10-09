import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TailGroup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Layout

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def tailSteps : List (Fin 4 × Nat) := [(0,2),(0,1),(1,2),(1,1),(2,2),(2,1),(3,2),(3,1)]

def tailCode (r : Ren) (ps : List (Fin 4 × Nat)) : List Instr :=
  ps.flatMap fun (g,len) => rootAt (tailBase len) g.val ++
    renInnerPair r.data[2*g.val] r.data[2*g.val+1] r.free len

def tailValues (v : Vector (BitVec 128) 8) (z : Nat → Nat → Nat → Int) :
    List (Fin 4 × Nat) → Vector (BitVec 128) 8
  | [] => v
  | (g,len)::ps => tailValues
      (packedValues v ⟨2*g.val,by omega⟩ ⟨2*g.val+1,by omega⟩ len (z g.val len)) z ps

theorem tailRun_ok (r : Ren) (ps : List (Fin 4 × Nat))
    (hl : ∀ p ∈ ps, p.2=1 ∨ p.2=2) (hr : GoodRen r)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Vector (BitVec 128) 8}
    {z : Nat → Nat → Nat → Int} (hbank : Bank s r.data v) (hconst : TailRoots s z)
    (k : ∀ t, VChg tailRegs s t → TailRoots t z →
      Bank t r.data (tailValues v z ps) → WP isa (.block rest) t Q) :
    WP isa (.block (tailCode r ps ++ rest)) s Q := by
  induction ps generalizing s v with
  | nil => exact k s (VChg.refl _ _) hconst hbank
  | cons p ps ih =>
    simp only [tailCode,List.flatMap_cons,List.append_assoc]
    have run := tailGroup_ok r p.1 p.2 (hl p (by simp)) hr
      (rest := tailCode r ps ++ rest) hbank hconst
      (fun s₁ hc₁ ht₁ hb₁ => by
        refine ih (fun p hp => hl p (List.mem_cons_of_mem _ hp)) hb₁ ht₁
          fun s₂ hc₂ ht₂ hb₂ => k s₂ (VChg.mono (hc₁.trans hc₂) ?_) ht₂ hb₂
        intro v hv
        simpa only [List.mem_append,or_self] using hv)
    simpa only [tailCode,List.append_assoc] using run

theorem tailSteps_valid : ∀ p ∈ tailSteps, p.2=1 ∨ p.2=2 := by
  simp only [tailSteps,List.mem_cons,List.not_mem_nil,or_false]
  intro p hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem renThree_good (outer : Bool) : GoodRen (renThree outer) := by
  refine ⟨renThree_injective outer,renThree_apart outer,?_,?_⟩
  · rw [renThree_data]
    decide
  · rw [renThree_free]
    decide

end VG.Proof.MlDsa.AArch64.Optimized
