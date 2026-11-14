module

-- separate module: The ordinary-field canonical/bounds transfer for the MixedMul8 machine slice (MixedMul8Field_split) costs 1.79s of proof versus 0.63s of imports; MixedBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulGeneric
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedMul8
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSchedule
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block

/-! Complete checked emitted field multiplication at MixedMul8Field. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def MixedMul8FieldCode : List Instr := ((mixedFnBlocks.drop 92).flatten.drop 9).take 402
def MixedMul8FieldMiddle : List Instr := ((mixedFnBlocks.drop 93).flatten.drop 15).take 316
def MixedMul8FieldFold : List Instr := ((mixedFnBlocks.drop 103).flatten.drop 11).take 28
def MixedMul8FieldTail : List Instr := ((mixedFnBlocks.drop 104).flatten.drop 7).take 20
def MixedMul8FieldFoldLoads : List Instr := loadsR .x30 pointMulFoldLowRegs 360

theorem MixedMul8Field_source : MixedMul8FieldCode=(mixedFnBlocks.flatten.drop 2953).take 402 := by
  have h := drop_flatten_prefix mixedFnBlocks 92 2944 9
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 402) h.symm

theorem MixedMul8Field_fold_hoist : hoistLoads .x30 MixedMul8FieldFold=
    some (MixedMul8FieldFoldLoads,pointMulFoldArith) := by lit_decide

theorem MixedMul8Field_split : MixedMul8FieldCode=
    MixedMul8Early++(MixedMul8FieldMiddle++(MixedMul8FieldFold++MixedMul8FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem MixedMul8Field_normalized : pointMulCanonicalZ2Code .x27 144 .x30 360 .x30 360=
    (MixedMul8Loads++pointMulRow0Z2Arithmetic)++
      (MixedMul8FieldMiddle++((MixedMul8FieldFoldLoads++pointMulFoldArith)++MixedMul8FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem MixedMul8Field_run (s : State) : runBlock isa MixedMul8FieldCode s=
    runBlock isa (pointMulCanonicalZ2Code .x27 144 .x30 360 .x30 360) s := by
  rw [MixedMul8Field_split,MixedMul8Field_normalized]
  exact append_run_eq (hoistLoads_run MixedMul8_hoist)
    (append_run_eq (fun _ => rfl)
      (append_run_eq (hoistLoads_run MixedMul8Field_fold_hoist) (fun _ => rfl))) s

theorem MixedMul8Field_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x27 pa size) (hb : Ptr s .x30 pb cap) (ht : PtrW s .x30 po room)
    (hA : 216≤size) (hB : 432≤cap) (hO : 432≤room)
    (hz : s.gpr .x2=0)
    (stable : StableInput s (off pa 144) (off po 360))
    (ha' : wordsVal s.mem (off pa 144) 0 9<fieldPrime)
    (hb' : wordsVal s.mem (off pb 360) 0 9<fieldPrime) :
    WP isa (.block MixedMul8FieldCode) s fun t =>
      wordsVal t.mem (off po 360) 0 9<fieldPrime ∧
      wordsVal t.mem (off po 360) 0 9=
        (wordsVal s.mem (off pa 144) 0 9*wordsVal s.mem (off pb 360) 0 9)%fieldPrime ∧
      t.gpr .x2=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointMulStreamClob s t ∧ Outside (off po 360) 0 72 s.mem t.mem := by
  have h := point_mul_canonicalz2_ok
    (a:=144) (b:=360) (o:=360) ha hb ht hA hB hO (by decide) (by decide) (by decide)
    hz (by decide) (by decide) (by decide) stable ha' hb'
  obtain ⟨t,ht,hpost⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(MixedMul8Field_run s).trans ht,hpost⟩

end VG.Proof.Mont.AArch64.P521Field
