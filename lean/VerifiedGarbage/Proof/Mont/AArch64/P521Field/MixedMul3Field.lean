module

-- separate module: The ordinary-field canonical/bounds transfer for the MixedMul3 machine slice (MixedMul3Field_normalized) costs 1.78s of proof versus 0.75s of imports; MixedBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulGeneric
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedMul3
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSchedule
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block

/-! Complete checked emitted field multiplication at MixedMul3Field. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def MixedMul3FieldCode : List Instr := ((mixedFnBlocks.drop 8).flatten.drop 7).take 404
def MixedMul3FieldMiddle : List Instr := ((mixedFnBlocks.drop 9).flatten.drop 14).take 317
def MixedMul3FieldFold : List Instr := ((mixedFnBlocks.drop 19).flatten.drop 11).take 28
def MixedMul3FieldTail : List Instr := ((mixedFnBlocks.drop 20).flatten.drop 7).take 20
def MixedMul3FieldFoldLoads : List Instr := loadsR .x30 pointMulFoldLowRegs 72

theorem MixedMul3Field_source : MixedMul3FieldCode=(mixedFnBlocks.flatten.drop 263).take 404 := by
  have h := drop_flatten_prefix mixedFnBlocks 8 256 7
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 404) h.symm

theorem MixedMul3Field_fold_hoist : hoistLoads .x30 MixedMul3FieldFold=
    some (MixedMul3FieldFoldLoads,pointMulFoldArith) := by lit_decide

theorem MixedMul3Field_split : MixedMul3FieldCode=
    MixedMul3Early++(MixedMul3FieldMiddle++(MixedMul3FieldFold++MixedMul3FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem MixedMul3Field_normalized : pointMulCanonicalCode .x27 144 .x28 72 .x30 72=
    (MixedMul3Loads++pointMulRow0Arithmetic)++
      (MixedMul3FieldMiddle++((MixedMul3FieldFoldLoads++pointMulFoldArith)++MixedMul3FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem MixedMul3Field_run (s : State) : runBlock isa MixedMul3FieldCode s=
    runBlock isa (pointMulCanonicalCode .x27 144 .x28 72 .x30 72) s := by
  rw [MixedMul3Field_split,MixedMul3Field_normalized]
  exact append_run_eq (hoistLoads_run MixedMul3_hoist)
    (append_run_eq (fun _ => rfl)
      (append_run_eq (hoistLoads_run MixedMul3Field_fold_hoist) (fun _ => rfl))) s

theorem MixedMul3Field_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x27 pa size) (hb : Ptr s .x28 pb cap) (ht : PtrW s .x30 po room)
    (hA : 216≤size) (hB : 144≤cap) (hO : 144≤room)
    (stable : StableInput s (off pa 144) (off po 72))
    (ha' : wordsVal s.mem (off pa 144) 0 9<fieldPrime)
    (hb' : wordsVal s.mem (off pb 72) 0 9<fieldPrime) :
    WP isa (.block MixedMul3FieldCode) s fun t =>
      wordsVal t.mem (off po 72) 0 9<fieldPrime ∧
      wordsVal t.mem (off po 72) 0 9=
        (wordsVal s.mem (off pa 144) 0 9*wordsVal s.mem (off pb 72) 0 9)%fieldPrime ∧
      t.gpr .x2=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointMulStreamClob s t ∧ Outside (off po 72) 0 72 s.mem t.mem := by
  have h := point_mul_canonical_ok
    (a:=144) (b:=72) (o:=72) ha hb ht hA hB hO (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) stable ha' hb'
  obtain ⟨t,ht,hpost⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(MixedMul3Field_run s).trans ht,hpost⟩

end VG.Proof.Mont.AArch64.P521Field
