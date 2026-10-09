import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Inverse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBatch

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Inverse (CS qt batch)

/-- Increasing inverse-layer gaps; the same seven groups occur in each pass. -/
def steps : List (Nat × Nat) := [(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(4,0)]

def indices (gap group : Nat) : List (Nat × Nat) :=
  (List.range gap).map fun j => (2*gap*group+j,2*gap*group+j+gap)

def pairs (st : CS) (ij : List (Nat × Nat)) : List PairRegs :=
  (List.range ij.length).map fun j => ⟨st.regs[ij[j]!.1]!,st.regs[ij[j]!.2]!,st.free[j]!⟩

def products (st : CS) (ij : List (Nat × Nat)) : List (VReg × VReg) :=
  (List.range ij.length).map fun j => (st.free[j]!,qt j)

/-- Discard accumulated code when computing only the register allocation. -/
def next (st : CS) (p : Nat × Nat) : CS :=
  let t := batch st (indices p.1 p.2)
  {code := [],regs := t.regs,free := t.free}

def before (i : Nat) : CS := (steps.take i).foldl next {}

def stagePairs (i : Nat) : List PairRegs :=
  pairs (before i) (indices steps[i]!.1 steps[i]!.2)

def stageProducts (i : Nat) : List (VReg × VReg) :=
  products (before i) (indices steps[i]!.1 steps[i]!.2)

theorem stage_products (i : Fin 7) (p : PairRegs) (hp : p∈stagePairs i.val) :
    ∃ temp, (p.free,temp)∈stageProducts i.val := by
  have h : ∀ i : Fin 7, ∀ p∈stagePairs i.val,
      ([VReg.v16,.v17,.v18,.v19].any fun temp => decide ((p.free,temp)∈stageProducts i.val))=true := by
    decide +kernel
  obtain ⟨temp,_,ht⟩ := List.any_eq_true.mp (h i p hp)
  exact ⟨temp,of_decide_eq_true ht⟩

/-- Small kernel-checked certificates discharge the actual register allocator's
read/write disjointness for all seven concrete arithmetic groups. -/
theorem stage_shape (i : Fin 7) : BatchShape (stagePairs i.val) (stageProducts i.val) := by
  constructor <;> revert i <;> first | (decide +kernel) | exact fun i p hp => stage_products i p hp

theorem stage_lengths (i : Fin 8) : (before i.val).regs.length=8 ∧ (before i.val).free.length=4 := by
  exact (show ∀ i : Fin 8, (before i.val).regs.length=8 ∧ (before i.val).free.length=4 by decide +kernel) i

theorem batch_code (st : CS) (ij : List (Nat × Nat)) :
    (batch st ij).code = st.code ++ (pairs st ij).flatMap PairRegs.code ++ multiplyCode (products st ij) := by
  simp only [batch,pairs,products,PairRegs.code,multiplyCode,List.flatMap_map,List.map_map,
    Function.comp_def,List.append_assoc]

theorem stage_empty (i : Fin 8) : (before i.val).code=[] := by
  exact (show ∀ i : Fin 8, (before i.val).code=[] by decide +kernel) i

theorem stage_next (i : Fin 7) :
    (batch (before i.val) (indices steps[i.val]!.1 steps[i.val]!.2)).regs=(before (i.val+1)).regs ∧
    (batch (before i.val) (indices steps[i.val]!.1 steps[i.val]!.2)).free=(before (i.val+1)).free := by
  exact (show ∀ i : Fin 7,
    (batch (before i.val) (indices steps[i.val]!.1 steps[i.val]!.2)).regs=(before (i.val+1)).regs ∧
    (batch (before i.val) (indices steps[i.val]!.1 steps[i.val]!.2)).free=(before (i.val+1)).free by decide +kernel) i

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
