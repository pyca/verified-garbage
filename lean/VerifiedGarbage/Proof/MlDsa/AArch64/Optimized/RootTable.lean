import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Slice
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.SliceFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! ## From `FiveSlice.lean` -/

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
