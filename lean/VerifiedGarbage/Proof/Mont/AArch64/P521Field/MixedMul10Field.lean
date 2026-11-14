module

-- separate module: The ordinary-field canonical/bounds transfer for the MixedMul10 machine slice (MixedMul10Field_normalized) costs 1.93s of proof versus 0.64s of imports; MixedBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulGeneric
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedMul10
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSchedule
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block

/-! Complete checked emitted field multiplication at MixedMul10Field. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def MixedMul10FieldCode : List Instr := ((mixedFnBlocks.drop 120).flatten.drop 9).take 402
def MixedMul10FieldMiddle : List Instr := ((mixedFnBlocks.drop 121).flatten.drop 15).take 316
def MixedMul10FieldFold : List Instr := ((mixedFnBlocks.drop 131).flatten.drop 11).take 28
def MixedMul10FieldTail : List Instr := ((mixedFnBlocks.drop 132).flatten.drop 7).take 20
def MixedMul10FieldFoldLoads : List Instr := loadsR .x30 pointMulFoldLowRegs 288

theorem MixedMul10Field_source : MixedMul10FieldCode=(mixedFnBlocks.flatten.drop 3849).take 402 := by
  have h := drop_flatten_prefix mixedFnBlocks 120 3840 9
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 402) h.symm

theorem MixedMul10Field_fold_hoist : hoistLoads .x30 MixedMul10FieldFold=
    some (MixedMul10FieldFoldLoads,pointMulFoldArith) := by lit_decide

theorem MixedMul10Field_split : MixedMul10FieldCode=
    MixedMul10Early++(MixedMul10FieldMiddle++(MixedMul10FieldFold++MixedMul10FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem MixedMul10Field_normalized : pointMulCanonicalZ2Code .x30 72 .x30 288 .x30 288=
    (MixedMul10Loads++pointMulRow0Z2Arithmetic)++
      (MixedMul10FieldMiddle++((MixedMul10FieldFoldLoads++pointMulFoldArith)++MixedMul10FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem MixedMul10Field_run (s : State) : runBlock isa MixedMul10FieldCode s=
    runBlock isa (pointMulCanonicalZ2Code .x30 72 .x30 288 .x30 288) s := by
  rw [MixedMul10Field_split,MixedMul10Field_normalized]
  exact append_run_eq (hoistLoads_run MixedMul10_hoist)
    (append_run_eq (fun _ => rfl)
      (append_run_eq (hoistLoads_run MixedMul10Field_fold_hoist) (fun _ => rfl))) s

theorem MixedMul10Field_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x30 pa size) (hb : Ptr s .x30 pb cap) (ht : PtrW s .x30 po room)
    (hA : 144≤size) (hB : 360≤cap) (hO : 360≤room)
    (hz : s.gpr .x2=0)
    (stable : StableInput s (off pa 72) (off po 288))
    (ha' : wordsVal s.mem (off pa 72) 0 9<fieldPrime)
    (hb' : wordsVal s.mem (off pb 288) 0 9<fieldPrime) :
    WP isa (.block MixedMul10FieldCode) s fun t =>
      wordsVal t.mem (off po 288) 0 9<fieldPrime ∧
      wordsVal t.mem (off po 288) 0 9=
        (wordsVal s.mem (off pa 72) 0 9*wordsVal s.mem (off pb 288) 0 9)%fieldPrime ∧
      t.gpr .x2=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointMulStreamClob s t ∧ Outside (off po 288) 0 72 s.mem t.mem := by
  have h := point_mul_canonicalz2_ok
    (a:=72) (b:=288) (o:=288) ha hb ht hA hB hO (by decide) (by decide) (by decide)
    hz (by decide) (by decide) (by decide) stable ha' hb'
  obtain ⟨t,ht,hpost⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(MixedMul10Field_run s).trans ht,hpost⟩

end VG.Proof.Mont.AArch64.P521Field
