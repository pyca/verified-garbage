module

-- separate module: The ordinary-field canonical/bounds transfer for the DoubleMul0 machine slice (DoubleMul0Field_normalized) costs 1.66s of proof versus 0.54s of imports; DoubleBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulGeneric
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleMul0
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSchedule
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block

/-! Complete checked emitted field multiplication at DoubleMul0Field. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def DoubleMul0FieldCode : List Instr := ((doubleFnBlocks.drop 18).flatten.drop 28).take 404
def DoubleMul0FieldMiddle : List Instr := ((doubleFnBlocks.drop 20).flatten.drop 3).take 317
def DoubleMul0FieldFold : List Instr := ((doubleFnBlocks.drop 30).flatten.drop 0).take 28
def DoubleMul0FieldTail : List Instr := ((doubleFnBlocks.drop 30).flatten.drop 28).take 20
def DoubleMul0FieldFoldLoads : List Instr := loadsR .x28 pointMulFoldLowRegs 144

theorem DoubleMul0Field_source : DoubleMul0FieldCode=(doubleFnBlocks.flatten.drop 604).take 404 := by
  have h := drop_flatten_prefix doubleFnBlocks 18 576 28
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 404) h.symm

theorem DoubleMul0Field_fold_hoist : hoistLoads .x28 DoubleMul0FieldFold=
    some (DoubleMul0FieldFoldLoads,pointMulFoldArith) := by lit_decide

theorem DoubleMul0Field_split : DoubleMul0FieldCode=
    DoubleMul0Early++(DoubleMul0FieldMiddle++(DoubleMul0FieldFold++DoubleMul0FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem DoubleMul0Field_normalized : pointMulCanonicalCode .x28 360 .x28 288 .x28 144=
    (DoubleMul0Loads++pointMulRow0Arithmetic)++
      (DoubleMul0FieldMiddle++((DoubleMul0FieldFoldLoads++pointMulFoldArith)++DoubleMul0FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem DoubleMul0Field_run (s : State) : runBlock isa DoubleMul0FieldCode s=
    runBlock isa (pointMulCanonicalCode .x28 360 .x28 288 .x28 144) s := by
  rw [DoubleMul0Field_split,DoubleMul0Field_normalized]
  exact append_run_eq (hoistLoads_run DoubleMul0_hoist)
    (append_run_eq (fun _ => rfl)
      (append_run_eq (hoistLoads_run DoubleMul0Field_fold_hoist) (fun _ => rfl))) s

theorem DoubleMul0Field_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x28 pa size) (hb : Ptr s .x28 pb cap) (ht : PtrW s .x28 po room)
    (hA : 432≤size) (hB : 360≤cap) (hO : 216≤room)
    (stable : StableInput s (off pa 360) (off po 144))
    (ha' : wordsVal s.mem (off pa 360) 0 9<fieldPrime)
    (hb' : wordsVal s.mem (off pb 288) 0 9<fieldPrime) :
    WP isa (.block DoubleMul0FieldCode) s fun t =>
      wordsVal t.mem (off po 144) 0 9<fieldPrime ∧
      wordsVal t.mem (off po 144) 0 9=
        (wordsVal s.mem (off pa 360) 0 9*wordsVal s.mem (off pb 288) 0 9)%fieldPrime ∧
      t.gpr .x2=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointMulStreamClob s t ∧ Outside (off po 144) 0 72 s.mem t.mem := by
  have h := point_mul_canonical_ok
    (a:=360) (b:=288) (o:=144) ha hb ht hA hB hO (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) stable ha' hb'
  obtain ⟨t,ht,hpost⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(DoubleMul0Field_run s).trans ht,hpost⟩

end VG.Proof.Mont.AArch64.P521Field
