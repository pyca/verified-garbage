module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Slice
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PackedBank
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InnerRun

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Layout
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Table
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
/-! ## From `FiveSlice.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/TailGroup.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def tailRegs : List VReg := [.v18,.v19,.v25,.v26,.v4] ++ liveRegs

def tailBase (len : Nat) : Reg := if len=2 then .x7 else .x8

structure TailRoots (s : State) (z : Nat → Nat → Nat → Int) : Prop where
  q : ∀ e < 4, vword (s.v .v16) e = 8380417#32
  range : ∀ g < 4, ∀ len, len=1 ∨ len=2 → ∀ e < 4, 0 ≤ z g len e ∧ z g len e < 8380417
  read : ∀ g < 4, ∀ len, len=1 ∨ len=2 → ∀ b ∈ [0,16],
    InRegions (s.rd++s.wr) (s.gpr (tailBase len)+BitVec.ofNat 64 (32*g+b)) 16
  root : ∀ g < 4, ∀ len, len=1 ∨ len=2 → ∀ e < 4,
    vword (s.mem.read (s.gpr (tailBase len)+BitVec.ofNat 64 (32*g)) 16) e =
      BitVec.ofInt 32 (z g len e)
  reciprocal : ∀ g < 4, ∀ len, len=1 ∨ len=2 → ∀ e < 4,
    vword (s.mem.read (s.gpr (tailBase len)+BitVec.ofNat 64 (32*g+16)) 16) e =
      BitVec.ofInt 32 (Optimized.reciprocal (z g len e))

theorem TailRoots.keep_of {vs : List VReg} {s t : State} {z : Nat → Nat → Nat → Int} (h : TailRoots s z)
    (hc : VChg vs s t) (hq : VReg.v16 ∉ vs) : TailRoots t z := by
  refine ⟨?_,h.range,?_,?_,?_⟩
  · intro e he
    rw [hc.get .v16 hq]
    exact h.q e he
  · simpa only [hc.rd,hc.wr,hc.gpr] using h.read
  · simpa only [hc.mem,hc.gpr] using h.root
  · simpa only [hc.mem,hc.gpr] using h.reciprocal

theorem TailRoots.keep {s t : State} {z : Nat → Nat → Nat → Int} (h : TailRoots s z)
    (hc : VChg tailRegs s t) : TailRoots t z := h.keep_of hc (by decide)

theorem GoodRen.packedClobs_mem {r : Ren} (hr : GoodRen r) (i j : Fin 8) :
    packedClobs r i j ⊆ tailRegs := by
  intro v hv
  simp only [packedClobs,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · exact List.mem_append_right _ hr.free
  · exact List.mem_append_right _ (hr.data i)
  · exact List.mem_append_right _ (hr.data j)

theorem tailGroup_ok (r : Ren) (g : Fin 4) (len : Nat) (hlen : len=1 ∨ len=2)
    (hr : GoodRen r) {s : State} {rest : List Instr} {Q : State → Prop}
    {values : Vector (BitVec 128) 8} {z : Nat → Nat → Nat → Int}
    (hbank : Bank s r.data values) (hconst : TailRoots s z)
    (k : ∀ t, VChg tailRegs s t → TailRoots t z →
      Bank t r.data (packedValues values ⟨2*g.val,by omega⟩ ⟨2*g.val+1,by omega⟩ len (z g.val len)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (rootAt (tailBase len) g.val ++
      renInnerPair r.data[2*g.val] r.data[2*g.val+1] r.free len ++ rest)) s Q := by
  let i : Fin 8 := ⟨2*g.val,by omega⟩
  let j : Fin 8 := ⟨2*g.val+1,by omega⟩
  rw [List.append_assoc]
  refine rootAt_ok (tailBase len) g.val (by omega) ?_
    (hconst.read g.val g.isLt len hlen 16 (by simp)) fun s₁ hc₁ hz₁ hb₁ => ?_
  · simpa only [Nat.add_zero] using hconst.read g.val g.isLt len hlen 0 (by simp)
  · have hp : ∀ v ∈ liveRegs, v ∉ [VReg.v18,.v19] := by decide
    have bank₁ : Bank s₁ r.data values := by
      intro a
      rw [hc₁.get _ (hp _ (hr.data a))]
      exact hbank a
    have hq₁ : ∀ e < 4, vword (s₁.v .v16) e = 8380417#32 := by
      intro e he
      rw [hc₁.get .v16]
      exact hconst.q e he
    refine packedBank_ok r i j len (by intro h; have := congrArg Fin.val h; simp only [i,j] at this; omega)
      hr bank₁ (hconst.range g.val g.isLt len hlen) ?_ ?_ hq₁ fun s₂ hc₂ hb₂ => ?_
    · rw [hz₁]
      exact hconst.root g.val g.isLt len hlen
    · rw [hb₁]
      exact hconst.reciprocal g.val g.isLt len hlen
    · have hc : VChg tailRegs s s₂ := VChg.mono (hc₁.trans hc₂) (by
        intro v hv
        rcases List.mem_append.mp hv with h | h
        · have hs : [VReg.v18,.v19] ⊆ tailRegs := by decide
          exact hs h
        · exact hr.packedClobs_mem i j h)
      exact k s₂ hc (hconst.keep hc) hb₂

end VG.Proof.MlDsa.AArch64.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/TailRun.lean`, which only this module imported.
section

@[expose] public section

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
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/FiveCore.lean`, which only this module imported.
section

/-! ## From `Normalize.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def positiveVector (v : BitVec 128) : BitVec 128 :=
  ofVWords (positiveWord (vword v 0)) (positiveWord (vword v 1))
    (positiveWord (vword v 2)) (positiveWord (vword v 3))

theorem positiveVector_word (v : BitVec 128) {e : Nat} (he : e < 4) :
    vword (positiveVector v) e = positiveWord (vword v e) := by
  rw [positiveVector, VG.AArch64.vword_ofVWords _ _ _ _ he]
  rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl <;> rfl

/-- Normalizing the complete bank neither assumes nor establishes canonical
representatives: the exact outputs are positive and below 3q. -/
theorem positive_many_ok (regs : List VReg) (hd : regs.Nodup)
    (ha : ∀ d ∈ regs, d ≠ .v4 ∧ d ≠ .v16)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀ e < 4, vword (s.v .v16) e = 8380417#32)
    (k : ∀ t, VChg (.v4::regs) s t →
      (∀ d ∈ regs, t.v d = positiveVector (s.v d)) → WP isa (.block rest) t Q) :
    WP isa (.block (regs.flatMap canon ++ rest)) s Q := by
  induction regs generalizing s with
  | nil => exact k s (VChg.refl _ _) (by simp)
  | cons d regs ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine positive_ok (ha d (by simp)).1 (ha d (by simp)).2 (by decide) hq
      fun s₁ hc₁ hv₁ => ?_
    have hdv : s₁.v d = positiveVector (s.v d) := by
      apply VG.AArch64.vec_ext
      intro e he
      rw [hv₁ e he,positiveVector_word _ he]
    have hq₁ : ∀ e < 4, vword (s₁.v .v16) e = 8380417#32 := by
      intro e he
      rw [hc₁.get .v16 (by simp [(ha d (by simp)).2.symm])]
      exact hq e he
    refine ih (List.nodup_cons.mp hd).2 (fun d hp => ha d (List.mem_cons_of_mem _ hp)) hq₁
      fun s₂ hc₂ hv₂ => k s₂ (VChg.mono (hc₁.trans hc₂) ?_) ?_
    · intro v hv
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hv ⊢
      grind only
    · intro a hm
      rcases List.mem_cons.mp hm with he | hm
      · subst a
        rw [hc₂.get d (by simp [(ha d (by simp)).1, (List.nodup_cons.mp hd).1]),hdv]
      · rw [hv₂ a hm,hc₁.get a ?_]
        have had : a ≠ d := by
          intro he
          exact (List.nodup_cons.mp hd).1 (he ▸ hm)
        simp [had,(ha a (List.mem_cons_of_mem _ hm)).1]

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `NormalizeBank.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem normalizeBank_ok (regs : Vector VReg 8) (hd : regs.toList.Nodup)
    (ha : ∀ d ∈ regs.toList, d ≠ .v4 ∧ d ≠ .v16)
    {s : State} {rest : List Instr} {Q : State → Prop} {values : Vector (BitVec 128) 8}
    (hb : Bank s regs values) (hq : ∀ e < 4, vword (s.v .v16) e = 8380417#32)
    (k : ∀ t, VChg (.v4::regs.toList) s t →
      Bank t regs (values.map positiveVector) → WP isa (.block rest) t Q) :
    WP isa (.block (regs.toList.flatMap canon ++ rest)) s Q := by
  refine positive_many_ok regs.toList hd ha hq fun t hc hv => k t hc ?_
  intro i
  have hi : i.val < regs.toList.length := by simp
  have hm : regs[i.val] ∈ regs.toList := by
    simpa only [Vector.getElem_toList] using List.getElem_mem hi
  rw [hv _ hm,hb i,Vector.getElem_map]

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `FiveCore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def fiveRegs : List VReg := outerRegs ++ tailRegs

def fiveCoreCode : List Instr := (renThree false).code ++ tailCode (renThree false) tailSteps ++
  (renThree false).data.toList.flatMap canon

def fiveValues (v : Vector (BitVec 128) 8) (zi zt : Nat → Nat → Nat → Int) : Vector (BitVec 128) 8 :=
  (tailValues (innerValues v zi outerSteps) zt tailSteps).map positiveVector

/-- The exact five fused inner layers, followed by positive normalization. -/
theorem fiveCore_ok {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Vector (BitVec 128) 8} {zi zt : Nat → Nat → Nat → Int}
    (hb : Bank s ({} : Ren).data v) (hi : InnerRoots s zi) (ht : TailRoots s zt)
    (k : ∀ t, VChg fiveRegs s t →
      Bank t (renThree false).data (fiveValues v zi zt) → WP isa (.block rest) t Q) :
    WP isa (.block (fiveCoreCode ++ rest)) s Q := by
  simp only [fiveCoreCode,List.append_assoc]
  refine innerThree_ok hb hi fun s₁ hc₁ _ hb₁ => ?_
  refine tailRun_ok (renThree false) tailSteps tailSteps_valid (renThree_good false)
    hb₁ (ht.keep_of hc₁ (by decide)) fun s₂ hc₂ ht₂ hb₂ => ?_
  have hd : (renThree false).data.toList.Nodup := by rw [renThree_data]; decide
  have ha : ∀ d ∈ (renThree false).data.toList, d ≠ VReg.v4 ∧ d ≠ VReg.v16 := by
    rw [renThree_data]
    decide
  refine normalizeBank_ok (renThree false).data hd ha hb₂ ht₂.q fun s₃ hc₃ hb₃ => k s₃ ?_ hb₃
  have hs : (.v4::(renThree false).data.toList) ⊆ tailRegs := by
    rw [renThree_data]
    decide
  refine VChg.mono ((hc₁.trans hc₂).trans (hc₃.mono hs)) ?_
  intro v hv
  simp only [fiveRegs,List.mem_append] at hv ⊢
  exact hv.elim id Or.inr

end VG.Proof.MlDsa.AArch64.Optimized

end
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def fiveSliceCode : List Instr :=
  (bankLoads ({} : Ren).data 16).map (fun p => Instr.ldrq p.1 .x2 p.2) ++ fiveCoreCode ++
  (bankLoads (renThree false).data 16).map (fun p => Instr.strq p.1 .x2 p.2)

def fiveSliceMem (s : State) (zi zt : Nat → Nat → Nat → Int) : Mem :=
  writeBank (fiveValues (readBank s.mem (s.gpr .x2) 16) zi zt) (s.gpr .x2) 16 s.mem

theorem fiveSlice_ok {s : State} {rest : List Instr} {Q : State → Prop}
    {zi zt : Nat → Nat → Nat → Int} (hi : InnerRoots s zi) (ht : TailRoots s zt)
    (hr : ∀ i : Fin 8, InRegions (s.rd++s.wr)
      (s.gpr .x2+BitVec.ofNat 64 (16*i.val)) 16)
    (hw : ∀ i : Fin 8, InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (16*i.val)) 16)
    (k : ∀ t, (∃ u, VChg fiveRegs s u ∧ VMem u t (fiveSliceMem s zi zt)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (fiveSliceCode ++ rest)) s Q := by
  have ho : ∀ i : Fin 8, (16*i.val)%16=0 ∧ 16*i.val<65536 := by intro i; omega
  have hs : ((bankLoads ({} : Ren).data 16).map Prod.fst) ⊆ outerRegs := by decide
  simp only [fiveSliceCode,List.append_assoc]
  refine loadBank_ok ({} : Ren).data 16 .x2 initial_good.injective ho hr fun s₁ hc₁ hb₁ => ?_
  have hc₁' := hc₁.mono hs
  refine fiveCore_ok hb₁ (hi.keep hc₁') (ht.keep_of hc₁' (by decide)) fun s₂ hc₂ hb₂ => ?_
  refine storeBank_ok (renThree false).data 16 .x2 ho hb₂ ?_ fun s₃ hm => ?_
  · intro i
    simpa only [hc₂.gpr,hc₂.wr,hc₁.gpr,hc₁.wr] using hw i
  · have hc : VChg fiveRegs s s₂ := VChg.mono (hc₁'.trans hc₂) (by
      intro v hv
      simp only [fiveRegs,List.mem_append] at hv ⊢
      exact hv.elim Or.inl id)
    have hm' : VMem s₂ s₃ (fiveSliceMem s zi zt) := by
      simpa only [fiveSliceMem,hc₂.mem,hc₁.mem,hc₂.gpr,hc₁.gpr] using hm
    exact k s₃ ⟨s₂,hc,hm'⟩

/-- The selected emitter uses precisely this proved slice plus its pointer increment. -/
theorem renFiveBody_eq : renFiveBody = fiveSliceCode ++ ([.addImm .x .x2 .x2 128] : List Instr) := by
  have hl : (bankLoads ({} : Ren).data 16).map (fun p => Instr.ldrq p.1 .x2 p.2) =
      dataRegs.zipIdx.flatMap (fun (v,i) => [Instr.ldrq v .x2 (16*i)]) := by rfl
  have hs : (bankLoads (renThree false).data 16).map (fun p => Instr.strq p.1 .x2 p.2) =
      (renThree false).data.toList.zipIdx.flatMap (fun (v,i) => [Instr.strq v .x2 (16*i)]) := by
    rw [renThree_data]
    rfl
  have ht : tailCode (renThree false) tailSteps = ((List.range 4).flatMap fun j =>
      packedAt .x7 2 (2*j) ++
        renInnerPair (renThree false).data[2*j]! (renThree false).data[2*j+1]! (renThree false).free 2 ++
      packedAt .x8 1 (4*j) ++
        renInnerPair (renThree false).data[2*j]! (renThree false).data[2*j+1]! (renThree false).free 1) := by
    simp only [tailCode,tailSteps,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      renThree_data,renThree_free]
    rfl
  simp only [renFiveBody,fiveSliceCode,fiveCoreCode,hl,hs,ht,List.append_assoc]

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `RootTable.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64

def innerOffset (gap : Nat) : Nat := if gap=4 then 0 else if gap=2 then 32 else 96

def tailOffset (len : Nat) : Nat := if len=2 then 224 else 352

def rootAddress (p : Addr) (u offset g b : Nat) : Addr :=
  p+BitVec.ofNat 64 (480*u+offset+32*g+b)

def expandedRegion (p : Addr) : Region := ⟨p,3904⟩

theorem inner_contains (p : Addr) {u gap g b : Nat} (hu : u<8) (hg : ValidGroup gap g)
    (hb : b=0 ∨ b=16) : (expandedRegion p).Contains (rootAddress p u (innerOffset gap) g b) 16 := by
  have h : 480*u+innerOffset gap+32*g+b+16 ≤ 3904 := by
    rcases hg with ⟨rfl,rfl⟩ | ⟨rfl,hg⟩ | ⟨rfl,hg⟩ <;>
      simp only [innerOffset,ite_true,show ¬2=4 by decide,show ¬1=4 by decide,show ¬1=2 by decide,ite_false] <;> omega
  exact Offset.contains_base p h (by omega)

theorem tail_contains (p : Addr) {u len g b : Nat} (hu : u<8) (hg : g<4)
    (hl : len=1 ∨ len=2) (hb : b=0 ∨ b=16) :
    (expandedRegion p).Contains (rootAddress p u (tailOffset len) g b) 16 := by
  have h : 480*u+tailOffset len+32*g+b+16 ≤ 3904 := by
    rcases hl with rfl | rfl <;> simp only [tailOffset,show ¬1=2 by decide,ite_false,ite_true] <;> omega
  exact Offset.contains_base p h (by omega)

/-- Logical values of the immutable prearranged inner table, independent of
its assembler symbol or host allocation. -/
structure RootTable (m : Mem) (p : Addr) (zi zt : Nat → Nat → Nat → Nat → Int) : Prop where
  inner_range : ∀ u < 8, ∀ gap g, ValidGroup gap g → ∀ e < 4,
    0 ≤ zi u gap g e ∧ zi u gap g e < 8380417
  tail_range : ∀ u < 8, ∀ g < 4, ∀ len, len=1 ∨ len=2 → ∀ e < 4,
    0 ≤ zt u g len e ∧ zt u g len e < 8380417
  inner_root : ∀ u < 8, ∀ gap g, ValidGroup gap g → ∀ e < 4,
    vword (m.read (rootAddress p u (innerOffset gap) g 0) 16) e = BitVec.ofInt 32 (zi u gap g e)
  inner_reciprocal : ∀ u < 8, ∀ gap g, ValidGroup gap g → ∀ e < 4,
    vword (m.read (rootAddress p u (innerOffset gap) g 16) 16) e =
      BitVec.ofInt 32 (reciprocal (zi u gap g e))
  tail_root : ∀ u < 8, ∀ g < 4, ∀ len, len=1 ∨ len=2 → ∀ e < 4,
    vword (m.read (rootAddress p u (tailOffset len) g 0) 16) e = BitVec.ofInt 32 (zt u g len e)
  tail_reciprocal : ∀ u < 8, ∀ g < 4, ∀ len, len=1 ∨ len=2 → ∀ e < 4,
    vword (m.read (rootAddress p u (tailOffset len) g 16) 16) e =
      BitVec.ofInt 32 (reciprocal (zt u g len e))

theorem RootTable.frame {m m' : Mem} {p : Addr} {zi zt : Nat → Nat → Nat → Nat → Int}
    {W : List Region} (h : RootTable m p zi zt) (hf : Frame W m m')
    (hd : ∀ r ∈ W, (expandedRegion p).Disjoint r) : RootTable m' p zi zt := by
  refine ⟨h.inner_range,h.tail_range,?_,?_,?_,?_⟩
  · intro u hu gap g hg e he
    rw [hf.read (inner_contains p hu hg (Or.inl rfl)) hd (by decide)]
    exact h.inner_root u hu gap g hg e he
  · intro u hu gap g hg e he
    rw [hf.read (inner_contains p hu hg (Or.inr rfl)) hd (by decide)]
    exact h.inner_reciprocal u hu gap g hg e he
  · intro u hu g hg len hl e he
    rw [hf.read (tail_contains p hu hg hl (Or.inl rfl)) hd (by decide)]
    exact h.tail_root u hu g hg len hl e he
  · intro u hu g hg len hl e he
    rw [hf.read (tail_contains p hu hg hl (Or.inr rfl)) hd (by decide)]
    exact h.tail_reciprocal u hu g hg len hl e he

structure FivePointers (s : State) (p : Addr) (u : Nat) : Prop where
  inner : ∀ gap, s.gpr (innerBase gap) = p+BitVec.ofNat 64 (480*u+innerOffset gap)
  tail : ∀ len, s.gpr (tailBase len) = p+BitVec.ofNat 64 (480*u+tailOffset len)

theorem FivePointers.inner_addr {s : State} {p : Addr} {u : Nat} (h : FivePointers s p u)
    (gap g b : Nat) : s.gpr (innerBase gap)+BitVec.ofNat 64 (32*g+b) =
      rootAddress p u (innerOffset gap) g b := by
  simp only [h.inner,rootAddress,BitVec.ofNat_add,BitVec.add_assoc]

theorem FivePointers.tail_addr {s : State} {p : Addr} {u : Nat} (h : FivePointers s p u)
    (len g b : Nat) : s.gpr (tailBase len)+BitVec.ofNat 64 (32*g+b) =
      rootAddress p u (tailOffset len) g b := by
  simp only [h.tail,rootAddress,BitVec.ofNat_add,BitVec.add_assoc]

theorem RootTable.roots {s : State} {p : Addr} {u : Nat} {zi zt : Nat → Nat → Nat → Nat → Int}
    (h : RootTable s.mem p zi zt) (hu : u<8) (hp : FivePointers s p u)
    (hr : expandedRegion p ∈ s.rd++s.wr) (hq : ∀ e < 4, vword (s.v .v16) e = 8380417#32) :
    InnerRoots s (zi u) ∧ TailRoots s (zt u) := by
  constructor
  · refine ⟨h.inner_range u hu,hq,?_,?_,?_⟩
    · intro gap g hg b hb
      rw [hp.inner_addr]
      exact ⟨_,hr,inner_contains p hu hg (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hb)⟩
    · intro gap g hg e he
      have ha := hp.inner_addr gap g 0
      simp only [Nat.add_zero] at ha
      rw [ha]
      exact h.inner_root u hu gap g hg e he
    · intro gap g hg e he
      rw [hp.inner_addr]
      exact h.inner_reciprocal u hu gap g hg e he
  · refine ⟨hq,h.tail_range u hu,?_,?_,?_⟩
    · intro g hg len hl b hb
      rw [hp.tail_addr]
      exact ⟨_,hr,tail_contains p hu hg hl (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hb)⟩
    · intro g hg len hl e he
      have ha := hp.tail_addr len g 0
      simp only [Nat.add_zero] at ha
      rw [ha]
      exact h.tail_root u hu g hg len hl e he
    · intro g hg len hl e he
      rw [hp.tail_addr]
      exact h.tail_reciprocal u hu g hg len hl e he

end VG.Proof.MlDsa.AArch64.Optimized

end
