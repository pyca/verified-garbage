import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Slice

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
