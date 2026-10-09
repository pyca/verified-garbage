import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedRun

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)

def finalLoads : List Instr := (bankLoads (regs 0) 128).map (fun p => Instr.ldrq p.1 .x2 p.2)
def finalSliceCode : List Instr := finalLoads ++ runCode finalLoad 0 7 ++ scaleCode ++ finalStoreCode
def finalAdvance : List Instr := [.addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1]

def finalValues (v : Vector (BitVec 128) 8) (q : BitVec 128) : Vector (BitVec 128) 8 :=
  canonicalValues (scaleValues (runValues finalZ 0 7 v)) q

def finalSliceMem (s : State) : Mem :=
  writeBank (finalValues (readBank s.mem (s.gpr .x2) 128) (s.v .v31)) (s.gpr .x2) 128 s.mem

theorem finalBody_eq : VG.Impl.MlDsa.AArch64.Optimized.Inverse.finalBody=
    finalSliceCode ++ finalAdvance := by decide +kernel

theorem finalSlice_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hf : FinalRoots s) (hs : ScaleRoots s)
    (hr : ∀ i : Fin 8, InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (128*i.val)) 16)
    (hw : ∀ i : Fin 8, InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (128*i.val)) 16)
    (k : ∀ t, (∃ mid, VChg runRegs s mid ∧ VMem mid t (finalSliceMem s)) → WP isa (.block rest) t Q) :
    WP isa (.block (finalSliceCode ++ rest)) s Q := by
  have ho : ∀ i : Fin 8, (128*i.val)%16=0 ∧ 128*i.val<65536 := by intro i; omega
  have hsub : ((bankLoads (regs 0) 128).map Prod.fst)⊆runRegs := by decide +kernel
  have hconst : ∀ r∈finalConstants, r∉runRegs := by decide
  simp only [finalSliceCode,finalLoads,List.append_assoc]
  refine loadBank_ok (regs 0) 128 .x2 initial_inj ho hr fun a hload hbank => ?_
  have hload' := hload.mono hsub
  have hf₁ := hf.frame hload' hconst
  refine run_ok finalPlan 0 7 (by decide) hbank hf₁ fun b hrun hf₂ hb => ?_
  have hsf : ScaleRoots b := by
    simpa only [ScaleRoots,hrun.get .v30 (by decide),hload'.get .v30 (by decide)] using hs
  refine scale_ok hb hsf hf₂.q fun c hscale hc => ?_
  refine finalStore_ok hc ?_ fun t ⟨d,hcanon,hm⟩ _ => ?_
  · intro i
    simpa only [hscale.wr,hscale.gpr,hrun.wr,hrun.gpr,hload.wr,hload.gpr] using hw i
  · have hframe : VChg runRegs s d := VChg.mono (((hload'.trans hrun).trans hscale).trans hcanon) (by
      intro r h
      simpa only [List.mem_append,or_self] using h)
    have hm' : VMem d t (finalSliceMem s) := by
      simpa only [show finalPlan.value=finalZ from rfl,finalSliceMem,finalValues,hscale.mem,hscale.gpr,
        hscale.get .v31 (by decide),hrun.mem,hrun.gpr,hrun.get .v31 (by decide),
        hload.mem,hload.gpr,hload'.get .v31 (by decide)] using hm
    exact k t ⟨d,hframe,hm'⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
