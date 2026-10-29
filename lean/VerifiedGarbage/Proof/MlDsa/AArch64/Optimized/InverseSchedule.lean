module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Inverse
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePairs
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Bank

import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
import VerifiedGarbage.Proof.Framework.Lit

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/InverseBatch.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def multiplyCode (ps : List (VReg × VReg)) : List Instr :=
  ps.map (fun p => .vop (.sqdmulh p.2 p.1 .v21)) ++
  (ps.map Prod.fst).map (fun d => .vop (.mul d d .v20)) ++
  ps.map (fun p => .vop (.mls p.1 p.2 .v31))

/-- Register-disjointness certificate for an inverse arithmetic batch.
Every reciprocal multiply consumes the difference from its own input pair. -/
structure BatchShape (ps : List PairRegs) (ms : List (VReg × VReg)) : Prop where
  pairs : (ps.flatMap PairRegs.all).Nodup
  data : (ms.map Prod.fst).Nodup
  temps : (ms.map Prod.snd).Nodup
  dataTemps : ∀ p∈ms, p.1∉ms.map Prod.snd
  tempsData : ∀ p∈ms, p.2∉ms.map Prod.fst
  rootData : .v20∉ms.map Prod.fst
  rootTemps : .v20∉ms.map Prod.snd
  recipTemps : .v21∉ms.map Prod.snd
  qData : .v31∉ms.map Prod.fst
  qTemps : .v31∉ms.map Prod.snd
  rootPairs : .v20∉pairWrites ps
  recipPairs : .v21∉pairWrites ps
  qPairs : .v31∉pairWrites ps
  sums : ∀ p∈ps, p.left∉ms.map Prod.snd ++ ms.map Prod.fst
  products : ∀ p∈ps, ∃ temp, (p.free,temp)∈ms

/-- Complete scheduled inverse batch: independent add/sub pairs followed by
high-product, low-product, and reduction phases. -/
theorem batch_ok (ps : List PairRegs) (ms : List (VReg × VReg)) (hshape : BatchShape ps ms)
    {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (hz : ∀ e<4, 0≤z e ∧ z e<8380417)
    (hzw : ∀ e<4, vword (s.v .v20) e=BitVec.ofInt 32 (z e))
    (hbw : ∀ e<4, vword (s.v .v21) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀ e<4, vword (s.v .v31) e=8380417#32)
    (k : ∀ t, VChg (pairWrites ps ++ ms.map Prod.snd ++ ms.map Prod.fst) s t →
      (∀ p∈ps, t.v p.left=VArr.s4.map2 (fun _ a b => a+b) (s.v p.left) (s.v p.right) ∧
        t.v p.free=fastVector (VArr.s4.map2 (fun _ a b => a-b) (s.v p.left) (s.v p.right)) z) →
      WP isa (.block rest) t Q) :
    WP isa (.block (ps.flatMap PairRegs.code ++ multiplyCode ms ++ rest)) s Q := by
  rw [List.append_assoc]
  refine pairs_ok ps hshape.pairs fun a ha hv => ?_
  refine multiply_batch_ok ms .v20 .v21 .v31 hshape.data hshape.temps hshape.dataTemps
    hshape.tempsData hshape.rootData hshape.rootTemps hshape.recipTemps hshape.qData hshape.qTemps
    hz ?_ ?_ ?_ fun t ht hm => ?_
  · rw [ha.get .v20 hshape.rootPairs]
    exact hzw
  · rw [ha.get .v21 hshape.recipPairs]
    exact hbw
  · rw [ha.get .v31 hshape.qPairs]
    exact hqw
  · refine k t (VChg.mono (ha.trans ht) ?_) ?_
    · intro r hr
      simpa only [List.mem_append,or_assoc] using hr
    · intro p hp
      constructor
      · rw [ht.get p.left (hshape.sums p hp)]
        exact (hv p hp).1
      · obtain ⟨temp,hmul⟩ := hshape.products p hp
        apply vec_ext
        intro e he
        rw [hm (p.free,temp) hmul e he,(hv p hp).2,fastVector_word _ _ he]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
end

end

@[expose] public section

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
