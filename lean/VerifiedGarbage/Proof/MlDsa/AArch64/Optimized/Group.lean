module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Bank

import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
import VerifiedGarbage.Proof.Framework.Lit

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/Rename.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem setBang_eq_set {α : Type} (v : Vector α 8) (j : Fin 8) (x : α) :
    v.set! j.val x = v.set j.val x := by
  apply Vector.ext
  intro k hk
  simp only [Vector.getElem_set!, Vector.getElem_set]

def pairValues (v : Vector (BitVec 128) 8) (i j : Fin 8) : Vector (BitVec 128) 8 :=
  (v.set i.val (VArr.s4.map2 (fun _ a b => a + b) v[i.val] v[j.val])).set j.val
    (VArr.s4.map2 (fun _ a b => a - b) v[i.val] v[j.val])

/-- The actual emitted two-instruction renaming step preserves the logical
bank and the free-register invariant needed by the next pair. -/
theorem renamePair_ok (r : Ren) (i j : Fin 8)
    {s : State} {rest : List Instr} {Q : State → Prop} {values : Vector (BitVec 128) 8}
    (h : Bank s r.data values)
    (hinj : Function.Injective (fun i : Fin 8 => r.data[i.val]))
    (hf : ∀ i : Fin 8, r.data[i.val] ≠ r.free)
    (k : ∀ t, VChg [r.free,r.data[i.val]] s t →
      Bank t (renamePair r i.val j.val).data (pairValues values i j) →
      Function.Injective (fun k : Fin 8 => (renamePair r i.val j.val).data[k.val]) →
      (∀ k : Fin 8, (renamePair r i.val j.val).data[k.val] ≠ (renamePair r i.val j.val).free) →
      WP isa (.block rest) t Q) :
    WP isa (.block (pairCode r i.val j.val ++ rest)) s Q := by
  simp only [pairCode, getElem!_pos r.data i.val i.isLt, getElem!_pos r.data j.val j.isLt,
    List.cons_append, List.nil_append]
  refine renamed_pair_ok (hf i) (hf j) fun t hc ha hb => ?_
  have ha' : t.v r.data[i.val] = VArr.s4.map2 (fun _ a b => a + b) (s.v r.data[i.val]) (s.v r.data[j.val]) := by
    apply vec_ext
    intro e he
    rw [ha e he, VG.AArch64.vword_map2 _ _ _ he]
  have hb' : t.v r.free = VArr.s4.map2 (fun _ a b => a - b) (s.v r.data[i.val]) (s.v r.data[j.val]) := by
    apply vec_ext
    intro e he
    rw [hb e he, VG.AArch64.vword_map2 _ _ _ he]
  have hs := rename_shape r.data j r.free hinj hf
  apply k t hc
  · change Bank t (r.data.set! j.val r.free) (pairValues values i j)
    rw [setBang_eq_set]
    exact h.pair hinj i j r.free hf hc ha' hb'
  · change Function.Injective (fun k : Fin 8 => (r.data.set! j.val r.free)[k.val])
    rw [setBang_eq_set]
    exact hs.1
  · change ∀ k : Fin 8, (r.data.set! j.val r.free)[k.val] ≠ r.data[j.val]!
    rw [setBang_eq_set, getElem!_pos r.data j.val j.isLt]
    exact hs.2

def afterPairs (r : Ren) : List (Fin 8 × Fin 8) → Ren
  | [] => r
  | (i,j) :: ps => afterPairs (renamePair r i.val j.val) ps

def pairOps (r : Ren) : List (Fin 8 × Fin 8) → List Instr
  | [] => []
  | (i,j) :: ps => pairCode r i.val j.val ++ pairOps (renamePair r i.val j.val) ps

def pairClobs (r : Ren) : List (Fin 8 × Fin 8) → List VReg
  | [] => []
  | (i,j) :: ps => [r.free,r.data[i.val]] ++ pairClobs (renamePair r i.val j.val) ps

def afterValues (values : Vector (BitVec 128) 8) : List (Fin 8 × Fin 8) → Vector (BitVec 128) 8
  | [] => values
  | (i,j) :: ps => afterValues (pairValues values i j) ps

theorem pairOps_same {r r' : Ren} (hd : r.data = r'.data) (hf : r.free = r'.free)
    (ps : List (Fin 8 × Fin 8)) : pairOps r ps = pairOps r' ps := by
  induction ps generalizing r r' with
  | nil => rfl
  | cons p ps ih =>
    simp only [pairOps]
    congr 1
    · simp only [pairCode, hd, hf]
    · exact ih (by simp only [renamePair, hd, hf]) (by simp only [renamePair, hd])

theorem afterPairs_same {r r' : Ren} (hd : r.data = r'.data) (hf : r.free = r'.free)
    (ps : List (Fin 8 × Fin 8)) :
    (afterPairs r ps).data = (afterPairs r' ps).data ∧
      (afterPairs r ps).free = (afterPairs r' ps).free := by
  induction ps generalizing r r' with
  | nil => exact ⟨hd,hf⟩
  | cons p ps ih =>
    exact ih (by simp only [renamePair, hd, hf]) (by simp only [renamePair, hd])

/-- Relate the compositional proof program to the generator's accumulated code. -/
theorem afterPairs_code (r : Ren) (ps : List (Fin 8 × Fin 8)) :
    (afterPairs r ps).code = r.code ++ pairOps r ps := by
  induction ps generalizing r with
  | nil => simp only [afterPairs, pairOps, List.append_nil]
  | cons p ps ih =>
    rw [afterPairs, ih]
    simp only [renamePair, pairOps, List.append_assoc]

theorem pairOps_ok (r : Ren) (ps : List (Fin 8 × Fin 8))
    {s : State} {rest : List Instr} {Q : State → Prop} {values : Vector (BitVec 128) 8}
    (h : Bank s r.data values)
    (hinj : Function.Injective (fun i : Fin 8 => r.data[i.val]))
    (hf : ∀ i : Fin 8, r.data[i.val] ≠ r.free)
    (k : ∀ t, VChg (pairClobs r ps) s t →
      Bank t (afterPairs r ps).data (afterValues values ps) →
      Function.Injective (fun i : Fin 8 => (afterPairs r ps).data[i.val]) →
      (∀ i : Fin 8, (afterPairs r ps).data[i.val] ≠ (afterPairs r ps).free) →
      WP isa (.block rest) t Q) :
    WP isa (.block (pairOps r ps ++ rest)) s Q := by
  induction ps generalizing r s values with
  | nil => exact k s (VChg.refl _ _) h hinj hf
  | cons p ps ih =>
    rw [pairOps, List.append_assoc]
    refine renamePair_ok r p.1 p.2 h hinj hf fun s₁ hc₁ h₁ hi₁ hf₁ => ?_
    refine ih _ h₁ hi₁ hf₁ fun s₂ hc₂ h₂ hi₂ hf₂ => ?_
    exact k s₂ (hc₁.trans hc₂) h₂ hi₂ hf₂

end VG.Proof.MlDsa.AArch64.Optimized
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

/-- The seven butterfly groups in a fused three-layer slice. -/
def ValidGroup (gap group : Nat) : Prop :=
  (gap = 4 ∧ group = 0) ∨ (gap = 2 ∧ (group = 0 ∨ group = 1)) ∨ (gap = 1 ∧ group < 4)

def groupSteps : Nat → Nat → List (Fin 8 × Fin 8)
  | 4, 0 => [(0,4),(1,5),(2,6),(3,7)]
  | 2, 0 => [(0,2),(1,3)]
  | 2, 1 => [(4,6),(5,7)]
  | 1, 0 => [(0,1)]
  | 1, 1 => [(2,3)]
  | 1, 2 => [(4,5)]
  | 1, 3 => [(6,7)]
  | _, _ => []

def groupProducts (r : Ren) (gap group : Nat) : List (VReg × VReg) :=
  ((List.range gap).map (fun j => r.data[2*gap*group+j+gap]!)).zipIdx.map
    fun (b,i) => (b,prodTemps[i]!)

def multiplyCode (ps : List (VReg × VReg)) : List Instr :=
  ps.map (fun p => .vop (.sqdmulh p.2 p.1 .v19)) ++
    (ps.map Prod.fst).map (fun d => .vop (.mul d d .v18)) ++
    ps.map (fun p => .vop (.mls p.1 p.2 .v16))

def groupStart (r : Ren) (gap group : Nat) (roots : List Instr) : Ren :=
  {r with code := r.code ++ roots ++ multiplyCode (groupProducts r gap group)}

def groupIndexedProducts (gap group : Nat) : List (Fin 8 × VReg) :=
  ((groupSteps gap group).map Prod.snd).zipIdx.map fun (i,k) => (i,prodTemps[k]!)

theorem groupProducts_indexed (r : Ren) (gap group : Nat) (hv : ValidGroup gap group) :
    groupProducts r gap group = (groupIndexedProducts gap group).map
      (fun p => (r.data[p.1.val],p.2)) := by
  rcases hv with ⟨rfl,rfl⟩ | ⟨rfl,hg⟩ | ⟨rfl,hg⟩
  · simp [groupProducts, groupIndexedProducts, groupSteps, List.range_succ, prodTemps]
    repeat constructor
  · rcases hg with rfl | rfl <;>
      simp [groupProducts, groupIndexedProducts, groupSteps, List.range_succ, prodTemps] <;> (repeat constructor)
  · have h : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;>
      simp [groupProducts, groupIndexedProducts, groupSteps, List.range_succ, prodTemps] <;> (repeat constructor)

theorem groupIndices_shape (gap group : Nat) (hv : ValidGroup gap group) :
    (groupIndexedProducts gap group).map Prod.fst = (groupSteps gap group).map Prod.snd ∧
    ((groupSteps gap group).map Prod.snd).Nodup ∧
    ((groupIndexedProducts gap group).map Prod.snd).Nodup ∧
    ∀ p ∈ groupIndexedProducts gap group, p.2 ∈ prodTemps := by
  rcases hv with ⟨rfl,rfl⟩ | ⟨rfl,hg⟩ | ⟨rfl,hg⟩
  · decide
  · rcases hg with rfl | rfl <;> decide
  · have h : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> decide

/-- The generator's list indexing selects exactly the seven well-bounded
logical schedules above. This is a kernel-checked generator identity. -/
theorem renGroup_eq (r : Ren) (gap group : Nat) (hv : ValidGroup gap group)
    (roots : List Instr) :
    renGroup r gap group roots = afterPairs (groupStart r gap group roots) (groupSteps gap group) := by
  rcases hv with ⟨rfl,rfl⟩ | ⟨rfl,hg⟩ | ⟨rfl,hg⟩
  · rfl
  · rcases hg with rfl | rfl <;> rfl
  · have h : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl

theorem renGroup_code (r : Ren) (gap group : Nat) (hv : ValidGroup gap group)
    (roots : List Instr) :
    (renGroup r gap group roots).code =
      (r.code ++ roots ++ multiplyCode (groupProducts r gap group)) ++
        pairOps (groupStart r gap group roots) (groupSteps gap group) := by
  rw [renGroup_eq r gap group hv roots, afterPairs_code]
  rfl

theorem renGroup_data (r : Ren) (gap group : Nat) (hv : ValidGroup gap group) (roots : List Instr) :
    (renGroup r gap group roots).data = (afterPairs r (groupSteps gap group)).data := by
  rw [renGroup_eq r gap group hv roots]
  exact (afterPairs_same (r := groupStart r gap group roots) (r' := r) rfl rfl _).1

theorem renGroup_free (r : Ren) (gap group : Nat) (hv : ValidGroup gap group) (roots : List Instr) :
    (renGroup r gap group roots).free = (afterPairs r (groupSteps gap group)).free := by
  rw [renGroup_eq r gap group hv roots]
  exact (afterPairs_same (r := groupStart r gap group roots) (r' := r) rfl rfl _).2

end VG.Proof.MlDsa.AArch64.Optimized
