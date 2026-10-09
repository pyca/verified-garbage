import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowFinal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalAdvance

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired (r0Pair finalPaired)

theorem allLow_flatMap (f : Nat → Nat → List Instr) :
    [0,1].flatMap (fun p => (List.range 4).flatMap (fun j => f p j))=
      allLow.flatMap (fun i => f i.1.val i.2.val) := by
  have he : ([0,1].flatMap fun p => (List.range 4).map fun j => (p,j))=
      allLow.map (fun i => (i.1.val,i.2.val)) := by decide
  have h := congrArg (fun xs : List (Nat × Nat) => xs.flatMap (fun i => f i.1 i.2)) he
  simpa only [List.flatMap_assoc,List.flatMap_map] using h

theorem lowRunCode_eq (g : Nat) :
    [0,1].flatMap (fun p => (List.range 4).flatMap (fun j => r0Pair g p j))=lowRunCode g allLow := by
  rw [allLow_flatMap]
  simp only [r0Pair_blocks,lowRunCode,lowRaw0,lowRaw1,lowOff]

theorem final_r0_eq (g : Nat) : finalPaired g=finalLowCode g++finalAdvance := by
  unfold finalPaired finalLowCode
  rw [finalPrefix_eq,lowRunCode_eq]
  simp only [List.append_assoc]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
