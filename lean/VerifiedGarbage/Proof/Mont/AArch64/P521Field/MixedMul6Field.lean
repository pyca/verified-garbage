module

-- separate module: The ordinary-field canonical/bounds transfer for the MixedMul6 machine slice (MixedMul6Field_normalized) costs 1.34s of proof versus 0.53s of imports; MixedBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulGeneric
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedMul6
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSchedule
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block

/-! Complete checked emitted field multiplication at MixedMul6Field. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def MixedMul6FieldCode : List Instr := ((mixedFnBlocks.drop 64).flatten.drop 7).take 404
def MixedMul6FieldMiddle : List Instr := ((mixedFnBlocks.drop 65).flatten.drop 14).take 317
def MixedMul6FieldFold : List Instr := ((mixedFnBlocks.drop 75).flatten.drop 11).take 28
def MixedMul6FieldTail : List Instr := ((mixedFnBlocks.drop 76).flatten.drop 7).take 20
def MixedMul6FieldFoldLoads : List Instr := loadsR .x30 pointMulFoldLowRegs 288

theorem MixedMul6Field_source : MixedMul6FieldCode=(mixedFnBlocks.flatten.drop 2055).take 404 := by
  have h := drop_flatten_prefix mixedFnBlocks 64 2048 7
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 404) h.symm

theorem MixedMul6Field_fold_hoist : hoistLoads .x30 MixedMul6FieldFold=
    some (MixedMul6FieldFoldLoads,pointMulFoldArith) := by lit_decide

theorem MixedMul6Field_split : MixedMul6FieldCode=
    MixedMul6Early++(MixedMul6FieldMiddle++(MixedMul6FieldFold++MixedMul6FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem MixedMul6Field_normalized : pointMulCanonicalCode .x30 216 .x27 0 .x30 288=
    (MixedMul6Loads++pointMulRow0Arithmetic)++
      (MixedMul6FieldMiddle++((MixedMul6FieldFoldLoads++pointMulFoldArith)++MixedMul6FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem MixedMul6Field_run (s : State) : runBlock isa MixedMul6FieldCode s=
    runBlock isa (pointMulCanonicalCode .x30 216 .x27 0 .x30 288) s := by
  rw [MixedMul6Field_split,MixedMul6Field_normalized]
  exact append_run_eq (hoistLoads_run MixedMul6_hoist)
    (append_run_eq (fun _ => rfl)
      (append_run_eq (hoistLoads_run MixedMul6Field_fold_hoist) (fun _ => rfl))) s

theorem MixedMul6Field_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x30 pa size) (hb : Ptr s .x27 pb cap) (ht : PtrW s .x30 po room)
    (hA : 288≤size) (hB : 72≤cap) (hO : 360≤room)
    (stable : StableInput s (off pa 216) (off po 288))
    (ha' : wordsVal s.mem (off pa 216) 0 9<fieldPrime)
    (hb' : wordsVal s.mem (off pb 0) 0 9<fieldPrime) :
    WP isa (.block MixedMul6FieldCode) s fun t =>
      wordsVal t.mem (off po 288) 0 9<fieldPrime ∧
      wordsVal t.mem (off po 288) 0 9=
        (wordsVal s.mem (off pa 216) 0 9*wordsVal s.mem (off pb 0) 0 9)%fieldPrime ∧
      t.gpr .x2=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointMulStreamClob s t ∧ Outside (off po 288) 0 72 s.mem t.mem := by
  have h := point_mul_canonical_ok
    (a:=216) (b:=0) (o:=288) ha hb ht hA hB hO (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) stable ha' hb'
  obtain ⟨t,ht,hpost⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(MixedMul6Field_run s).trans ht,hpost⟩

end VG.Proof.Mont.AArch64.P521Field
