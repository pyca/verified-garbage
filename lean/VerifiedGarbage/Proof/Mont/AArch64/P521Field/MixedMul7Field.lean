module

-- separate module: The ordinary-field canonical/bounds transfer for the MixedMul7 machine slice (MixedMul7Field_normalized) costs 2.02s of proof versus 0.63s of imports; MixedBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulGeneric
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedMul7
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSchedule
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block

/-! Complete checked emitted field multiplication at MixedMul7Field. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def MixedMul7FieldCode : List Instr := ((mixedFnBlocks.drop 76).flatten.drop 27).take 402
def MixedMul7FieldMiddle : List Instr := ((mixedFnBlocks.drop 78).flatten.drop 1).take 316
def MixedMul7FieldFold : List Instr := ((mixedFnBlocks.drop 87).flatten.drop 29).take 28
def MixedMul7FieldTail : List Instr := ((mixedFnBlocks.drop 88).flatten.drop 25).take 20
def MixedMul7FieldFoldLoads : List Instr := loadsR .x30 pointMulFoldLowRegs 144

theorem MixedMul7Field_source : MixedMul7FieldCode=(mixedFnBlocks.flatten.drop 2459).take 402 := by
  have h := drop_flatten_prefix mixedFnBlocks 76 2432 27
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 402) h.symm

theorem MixedMul7Field_fold_hoist : hoistLoads .x30 MixedMul7FieldFold=
    some (MixedMul7FieldFoldLoads,pointMulFoldArith) := by lit_decide

theorem MixedMul7Field_split : MixedMul7FieldCode=
    MixedMul7Early++(MixedMul7FieldMiddle++(MixedMul7FieldFold++MixedMul7FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem MixedMul7Field_normalized : pointMulCanonicalZ2Code .x30 216 .x30 144 .x30 144=
    (MixedMul7Loads++pointMulRow0Z2Arithmetic)++
      (MixedMul7FieldMiddle++((MixedMul7FieldFoldLoads++pointMulFoldArith)++MixedMul7FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem MixedMul7Field_run (s : State) : runBlock isa MixedMul7FieldCode s=
    runBlock isa (pointMulCanonicalZ2Code .x30 216 .x30 144 .x30 144) s := by
  rw [MixedMul7Field_split,MixedMul7Field_normalized]
  exact append_run_eq (hoistLoads_run MixedMul7_hoist)
    (append_run_eq (fun _ => rfl)
      (append_run_eq (hoistLoads_run MixedMul7Field_fold_hoist) (fun _ => rfl))) s

theorem MixedMul7Field_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x30 pa size) (hb : Ptr s .x30 pb cap) (ht : PtrW s .x30 po room)
    (hA : 288≤size) (hB : 216≤cap) (hO : 216≤room)
    (hz : s.gpr .x2=0)
    (stable : StableInput s (off pa 216) (off po 144))
    (ha' : wordsVal s.mem (off pa 216) 0 9<fieldPrime)
    (hb' : wordsVal s.mem (off pb 144) 0 9<fieldPrime) :
    WP isa (.block MixedMul7FieldCode) s fun t =>
      wordsVal t.mem (off po 144) 0 9<fieldPrime ∧
      wordsVal t.mem (off po 144) 0 9=
        (wordsVal s.mem (off pa 216) 0 9*wordsVal s.mem (off pb 144) 0 9)%fieldPrime ∧
      t.gpr .x2=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointMulStreamClob s t ∧ Outside (off po 144) 0 72 s.mem t.mem := by
  have h := point_mul_canonicalz2_ok
    (a:=216) (b:=144) (o:=144) ha hb ht hA hB hO (by decide) (by decide) (by decide)
    hz (by decide) (by decide) (by decide) stable ha' hb'
  obtain ⟨t,ht,hpost⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(MixedMul7Field_run s).trans ht,hpost⟩

end VG.Proof.Mont.AArch64.P521Field
