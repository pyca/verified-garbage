module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Inverse
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePairs
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Bank
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `MlDsa.AArch64.Optimized.InverseSchedule`, which only this module used -/

section

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

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def regs (i : Nat) : Vector VReg 8 := Vector.ofFn fun k => (before i).regs[k.val]!

def leftSide (i k : Nat) : Prop :=
  2*steps[i]!.1*steps[i]!.2≤k ∧ k<2*steps[i]!.1*steps[i]!.2+steps[i]!.1
instance (i k : Nat) : Decidable (leftSide i k) := inferInstanceAs (Decidable (_ ∧ _))
def rightSide (i k : Nat) : Prop :=
  2*steps[i]!.1*steps[i]!.2+steps[i]!.1≤k ∧ k<2*steps[i]!.1*steps[i]!.2+2*steps[i]!.1
instance (i k : Nat) : Decidable (rightSide i k) := inferInstanceAs (Decidable (_ ∧ _))

def leftSource (i : Nat) (k : Fin 8) : Fin 8 :=
  ⟨(if rightSide i k.val then k.val-steps[i]!.1 else k.val)%8,Nat.mod_lt _ (by decide)⟩
def rightSource (i : Nat) (k : Fin 8) : Fin 8 :=
  ⟨(if leftSide i k.val then k.val+steps[i]!.1 else k.val)%8,Nat.mod_lt _ (by decide)⟩
def stagePair (i k : Nat) : PairRegs := (stagePairs i)[k%steps[i]!.1]!
def stageClobs (i : Nat) : List VReg :=
  pairWrites (stagePairs i) ++ (stageProducts i).map Prod.snd ++ (stageProducts i).map Prod.fst

def stageValues (i : Nat) (v : Vector (BitVec 128) 8) (z : Nat → Int) : Vector (BitVec 128) 8 :=
  Vector.ofFn fun k =>
    if leftSide i k.val then VArr.s4.map2 (fun _ a b => a+b) v[(leftSource i k).val] v[(rightSource i k).val]
    else if rightSide i k.val then fastVector
      (VArr.s4.map2 (fun _ a b => a-b) v[(leftSource i k).val] v[(rightSource i k).val]) z
    else v[k.val]

/-- Finite register-geometry certificate, independent of coefficient values. -/
theorem stage_geometry (i : Fin 7) (k : Fin 8) :
    if leftSide i.val k.val then
      stagePair i.val k.val∈stagePairs i.val ∧
      (regs (i.val+1))[k.val]=(stagePair i.val k.val).left ∧
      (stagePair i.val k.val).left=(regs i.val)[(leftSource i.val k).val] ∧
      (stagePair i.val k.val).right=(regs i.val)[(rightSource i.val k).val]
    else if rightSide i.val k.val then
      stagePair i.val k.val∈stagePairs i.val ∧
      (regs (i.val+1))[k.val]=(stagePair i.val k.val).free ∧
      (stagePair i.val k.val).left=(regs i.val)[(leftSource i.val k).val] ∧
      (stagePair i.val k.val).right=(regs i.val)[(rightSource i.val k).val]
    else (regs (i.val+1))[k.val]=(regs i.val)[k.val] ∧ (regs i.val)[k.val]∉stageClobs i.val := by
  revert i k
  decide +kernel

/-- One concrete renamed group updates the logical bank exactly, regardless
of its initial representatives. -/
theorem stage_ok (i : Fin 7) {v : Vector (BitVec 128) 8}
    {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (hbank : Bank s (regs i.val) v)
    (hz : ∀ e<4, 0≤z e ∧ z e<8380417)
    (hzw : ∀ e<4, vword (s.v .v20) e=BitVec.ofInt 32 (z e))
    (hbw : ∀ e<4, vword (s.v .v21) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀ e<4, vword (s.v .v31) e=8380417#32)
    (k : ∀ t, VChg (stageClobs i.val) s t →
      Bank t (regs (i.val+1)) (stageValues i.val v z) → WP isa (.block rest) t Q) :
    WP isa (.block ((stagePairs i.val).flatMap PairRegs.code ++ multiplyCode (stageProducts i.val) ++ rest)) s Q := by
  refine batch_ok _ _ (stage_shape i) hz hzw hbw hqw fun t ht hv => k t ht ?_
  intro j
  have hg := stage_geometry i j
  change t.v (regs (i.val+1))[j.val] = (stageValues i.val v z)[j.val]
  simp only [stageValues,Vector.getElem_ofFn]
  by_cases hl : leftSide i.val j.val
  · rw [ite_eq_left hl] at hg ⊢
    rw [hg.2.1,(hv _ hg.1).1,hg.2.2.1,hg.2.2.2,hbank (leftSource i.val j),hbank (rightSource i.val j)]
  · rw [ite_eq_right hl] at hg ⊢
    by_cases hr : rightSide i.val j.val
    · rw [ite_eq_left hr] at hg ⊢
      rw [hg.2.1,(hv _ hg.1).2,hg.2.2.1,hg.2.2.2,hbank (leftSource i.val j),hbank (rightSource i.val j)]
    · rw [ite_eq_right hr] at hg ⊢
      rw [hg.1,ht.get _ hg.2,hbank j]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
