import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalSlice
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MultiplyInverse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedRun

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)

def rawFinalStores : List Instr := (bankLoads (regs 7) 128).map (fun p => Instr.strq p.1 .x2 p.2)
def rawFinalSliceCode : List Instr := finalLoads ++ runCode finalLoad 0 7 ++ scaleCode ++ rawFinalStores

def rawFinalValues (v : Vector (BitVec 128) 8) : Vector (BitVec 128) 8 :=
  scaleValues (runValues finalZ 0 7 v)

def rawFinalSliceMem (s : State) : Mem :=
  writeBank (rawFinalValues (readBank s.mem (s.gpr .x2) 128)) (s.gpr .x2) 128 s.mem

theorem rawFinalBody_eq : VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.rawFinalBody=
    rawFinalSliceCode ++ finalAdvance := by decide +kernel

theorem rawFinalSlice_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hf : FinalRoots s) (hs : ScaleRoots s)
    (hr : ∀ i : Fin 8, InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (128*i.val)) 16)
    (hw : ∀ i : Fin 8, InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (128*i.val)) 16)
    (k : ∀ t, (∃ mid, VChg runRegs s mid ∧ VMem mid t (rawFinalSliceMem s)) → WP isa (.block rest) t Q) :
    WP isa (.block (rawFinalSliceCode ++ rest)) s Q := by
  have ho : ∀ i : Fin 8, (128*i.val)%16=0 ∧ 128*i.val<65536 := by intro i; omega
  have hsub : ((bankLoads (regs 0) 128).map Prod.fst)⊆runRegs := by decide +kernel
  have hconst : ∀ r∈finalConstants, r∉runRegs := by decide
  simp only [rawFinalSliceCode,finalLoads,List.append_assoc]
  refine loadBank_ok (regs 0) 128 .x2 initial_inj ho hr fun a hload hbank => ?_
  have hload' := hload.mono hsub
  have hf₁ := hf.frame hload' hconst
  refine run_ok finalPlan 0 7 (by decide) hbank hf₁ fun b hrun hf₂ hb => ?_
  have hsf : ScaleRoots b := by
    simpa only [ScaleRoots,hrun.get .v30 (by decide),hload'.get .v30 (by decide)] using hs
  refine scale_ok hb hsf hf₂.q fun c hscale hc => ?_
  refine storeBank_ok (regs 7) 128 .x2 ho hc ?_ fun t hm => ?_
  · intro i
    simpa only [hscale.wr,hscale.gpr,hrun.wr,hrun.gpr,hload.wr,hload.gpr] using hw i
  · have hframe : VChg runRegs s c := VChg.mono ((hload'.trans hrun).trans hscale) (by
      intro r h
      simpa only [List.mem_append,or_self] using h)
    have hm' : VMem c t (rawFinalSliceMem s) := by
      simpa only [show finalPlan.value=finalZ from rfl,rawFinalSliceMem,rawFinalValues,hscale.mem,hscale.gpr,
        hrun.mem,hrun.gpr,hload.mem,hload.gpr] using hm
    exact k t ⟨c,hframe,hm'⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
