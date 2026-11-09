module

-- separate module: The ordinary-field canonical/bounds transfer for the MixedMul4 machine slice (MixedMul4Field_normalized) costs 1.86s of proof versus 0.56s of imports; MixedBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulGeneric
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedMul4
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSchedule
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block

/-! Complete checked emitted field multiplication at MixedMul4Field. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def MixedMul4FieldCode : List Instr := ((mixedFnBlocks.drop 20).flatten.drop 27).take 402
def MixedMul4FieldMiddle : List Instr := ((mixedFnBlocks.drop 22).flatten.drop 1).take 316
def MixedMul4FieldFold : List Instr := ((mixedFnBlocks.drop 31).flatten.drop 29).take 28
def MixedMul4FieldTail : List Instr := ((mixedFnBlocks.drop 32).flatten.drop 25).take 20
def MixedMul4FieldFoldLoads : List Instr := loadsR .x30 pointMulFoldLowRegs 144

theorem MixedMul4Field_source : MixedMul4FieldCode=(mixedFnBlocks.flatten.drop 667).take 402 := by
  have h := drop_flatten_prefix mixedFnBlocks 20 640 27
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 402) h.symm

theorem MixedMul4Field_fold_hoist : hoistLoads .x30 MixedMul4FieldFold=
    some (MixedMul4FieldFoldLoads,pointMulFoldArith) := by lit_decide

theorem MixedMul4Field_split : MixedMul4FieldCode=
    MixedMul4Early++(MixedMul4FieldMiddle++(MixedMul4FieldFold++MixedMul4FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem MixedMul4Field_normalized : pointMulCanonicalZ2Code .x30 0 .x28 0 .x30 144=
    (MixedMul4Loads++pointMulRow0Z2Arithmetic)++
      (MixedMul4FieldMiddle++((MixedMul4FieldFoldLoads++pointMulFoldArith)++MixedMul4FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem MixedMul4Field_run (s : State) : runBlock isa MixedMul4FieldCode s=
    runBlock isa (pointMulCanonicalZ2Code .x30 0 .x28 0 .x30 144) s := by
  rw [MixedMul4Field_split,MixedMul4Field_normalized]
  exact append_run_eq (hoistLoads_run MixedMul4_hoist)
    (append_run_eq (fun _ => rfl)
      (append_run_eq (hoistLoads_run MixedMul4Field_fold_hoist) (fun _ => rfl))) s

theorem MixedMul4Field_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x30 pa size) (hb : Ptr s .x28 pb cap) (ht : PtrW s .x30 po room)
    (hA : 72≤size) (hB : 72≤cap) (hO : 216≤room)
    (hz : s.gpr .x2=0)
    (stable : StableInput s (off pa 0) (off po 144))
    (ha' : wordsVal s.mem (off pa 0) 0 9<fieldPrime)
    (hb' : wordsVal s.mem (off pb 0) 0 9<fieldPrime) :
    WP isa (.block MixedMul4FieldCode) s fun t =>
      wordsVal t.mem (off po 144) 0 9<fieldPrime ∧
      wordsVal t.mem (off po 144) 0 9=
        (wordsVal s.mem (off pa 0) 0 9*wordsVal s.mem (off pb 0) 0 9)%fieldPrime ∧
      t.gpr .x2=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointMulStreamClob s t ∧ Outside (off po 144) 0 72 s.mem t.mem := by
  have h := point_mul_canonicalz2_ok
    (a:=0) (b:=0) (o:=144) ha hb ht hA hB hO (by decide) (by decide) (by decide)
    hz (by decide) (by decide) (by decide) stable ha' hb'
  obtain ⟨t,ht,hpost⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(MixedMul4Field_run s).trans ht,hpost⟩

end VG.Proof.Mont.AArch64.P521Field
