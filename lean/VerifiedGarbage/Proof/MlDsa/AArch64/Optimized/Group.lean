import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Rename

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
