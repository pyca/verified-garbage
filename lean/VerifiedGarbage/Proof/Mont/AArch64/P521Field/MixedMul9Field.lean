module

-- separate module: The ordinary-field canonical/bounds transfer for the MixedMul9 machine slice (MixedMul9Field_normalized) costs 2.25s of proof versus 0.64s of imports; MixedBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulGeneric
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedMul9
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSchedule
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block

/-! Complete checked emitted field multiplication at MixedMul9Field. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def MixedMul9FieldCode : List Instr := ((mixedFnBlocks.drop 107).flatten.drop 23).take 402
def MixedMul9FieldMiddle : List Instr := ((mixedFnBlocks.drop 108).flatten.drop 29).take 316
def MixedMul9FieldFold : List Instr := ((mixedFnBlocks.drop 118).flatten.drop 25).take 28
def MixedMul9FieldTail : List Instr := ((mixedFnBlocks.drop 119).flatten.drop 21).take 20
def MixedMul9FieldFoldLoads : List Instr := loadsR .x30 pointMulFoldLowRegs 216

theorem MixedMul9Field_source : MixedMul9FieldCode=(mixedFnBlocks.flatten.drop 3447).take 402 := by
  have h := drop_flatten_prefix mixedFnBlocks 107 3424 23
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 402) h.symm

theorem MixedMul9Field_fold_hoist : hoistLoads .x30 MixedMul9FieldFold=
    some (MixedMul9FieldFoldLoads,pointMulFoldArith) := by lit_decide

theorem MixedMul9Field_split : MixedMul9FieldCode=
    MixedMul9Early++(MixedMul9FieldMiddle++(MixedMul9FieldFold++MixedMul9FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem MixedMul9Field_normalized : pointMulCanonicalZ2Code .x27 72 .x30 216 .x30 216=
    (MixedMul9Loads++pointMulRow0Z2Arithmetic)++
      (MixedMul9FieldMiddle++((MixedMul9FieldFoldLoads++pointMulFoldArith)++MixedMul9FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem MixedMul9Field_run (s : State) : runBlock isa MixedMul9FieldCode s=
    runBlock isa (pointMulCanonicalZ2Code .x27 72 .x30 216 .x30 216) s := by
  rw [MixedMul9Field_split,MixedMul9Field_normalized]
  exact append_run_eq (hoistLoads_run MixedMul9_hoist)
    (append_run_eq (fun _ => rfl)
      (append_run_eq (hoistLoads_run MixedMul9Field_fold_hoist) (fun _ => rfl))) s

theorem MixedMul9Field_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x27 pa size) (hb : Ptr s .x30 pb cap) (ht : PtrW s .x30 po room)
    (hA : 144≤size) (hB : 288≤cap) (hO : 288≤room)
    (hz : s.gpr .x2=0)
    (stable : StableInput s (off pa 72) (off po 216))
    (ha' : wordsVal s.mem (off pa 72) 0 9<fieldPrime)
    (hb' : wordsVal s.mem (off pb 216) 0 9<fieldPrime) :
    WP isa (.block MixedMul9FieldCode) s fun t =>
      wordsVal t.mem (off po 216) 0 9<fieldPrime ∧
      wordsVal t.mem (off po 216) 0 9=
        (wordsVal s.mem (off pa 72) 0 9*wordsVal s.mem (off pb 216) 0 9)%fieldPrime ∧
      t.gpr .x2=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointMulStreamClob s t ∧ Outside (off po 216) 0 72 s.mem t.mem := by
  have h := point_mul_canonicalz2_ok
    (a:=72) (b:=216) (o:=216) ha hb ht hA hB hO (by decide) (by decide) (by decide)
    hz (by decide) (by decide) (by decide) stable ha' hb'
  obtain ⟨t,ht,hpost⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(MixedMul9Field_run s).trans ht,hpost⟩

end VG.Proof.Mont.AArch64.P521Field
