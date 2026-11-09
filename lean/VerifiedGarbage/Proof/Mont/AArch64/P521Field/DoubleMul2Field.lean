module

-- separate module: The ordinary-field canonical/bounds transfer for the DoubleMul2 machine slice (DoubleMul2Field_normalized) costs 1.54s of proof versus 0.64s of imports; DoubleBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulGeneric
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleMul2
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSchedule
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block

/-! Complete checked emitted field multiplication at DoubleMul2Field. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def DoubleMul2FieldCode : List Instr := ((doubleFnBlocks.drop 75).flatten.drop 22).take 392
def DoubleMul2FieldMiddle : List Instr := ((doubleFnBlocks.drop 76).flatten.drop 29).take 316
def DoubleMul2FieldFold : List Instr := ((doubleFnBlocks.drop 86).flatten.drop 25).take 28
def DoubleMul2FieldTail : List Instr := ((doubleFnBlocks.drop 87).flatten.drop 21).take 9
def DoubleMul2FieldFoldLoads : List Instr := loadsR .x28 pointMulFoldLowRegs 360

theorem DoubleMul2Field_source : DoubleMul2FieldCode=(doubleFnBlocks.flatten.drop 2422).take 392 := by
  have h := drop_flatten_prefix doubleFnBlocks 75 2400 22
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 392) h.symm

theorem DoubleMul2Field_fold_hoist : hoistLoads .x28 DoubleMul2FieldFold=
    some (DoubleMul2FieldFoldLoads,pointMulWeakArith) := by lit_decide

theorem DoubleMul2Field_split : DoubleMul2FieldCode=
    DoubleMul2Early++(DoubleMul2FieldMiddle++(DoubleMul2FieldFold++DoubleMul2FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem DoubleMul2Field_normalized : pointMulWeakCode .x28 432 .x28 144 .x28 360=
    (DoubleMul2Loads++pointMulRow0Arithmetic)++
      (DoubleMul2FieldMiddle++((DoubleMul2FieldFoldLoads++pointMulWeakArith)++DoubleMul2FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem DoubleMul2Field_run (s : State) : runBlock isa DoubleMul2FieldCode s=
    runBlock isa (pointMulWeakCode .x28 432 .x28 144 .x28 360) s := by
  rw [DoubleMul2Field_split,DoubleMul2Field_normalized]
  exact append_run_eq (hoistLoads_run DoubleMul2_hoist)
    (append_run_eq (fun _ => rfl)
      (append_run_eq (hoistLoads_run DoubleMul2Field_fold_hoist) (fun _ => rfl))) s

theorem DoubleMul2Field_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x28 pa size) (hb : Ptr s .x28 pb cap) (ht : PtrW s .x28 po room)
    (hA : 504≤size) (hB : 216≤cap) (hO : 432≤room)
    (stable : StableInput s (off pa 432) (off po 360))
    (ha' : wordsVal s.mem (off pa 432) 0 9<fieldPrime)
    (hb' : wordsVal s.mem (off pb 144) 0 9<fieldPrime) :
    WP isa (.block DoubleMul2FieldCode) s fun t =>
      wordsVal t.mem (off po 360) 0 9<2*fieldPrime ∧
      wordsVal t.mem (off po 360) 0 9%fieldPrime=
        (wordsVal s.mem (off pa 432) 0 9*wordsVal s.mem (off pb 144) 0 9)%fieldPrime ∧
      t.gpr .x2=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointMulStreamClob s t ∧ Outside (off po 360) 0 72 s.mem t.mem := by
  have h := point_mul_weak_ok
    (a:=432) (b:=144) (o:=360) ha hb ht hA hB hO (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) stable ha' hb'
  obtain ⟨t,ht,hpost⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(DoubleMul2Field_run s).trans ht,hpost⟩

end VG.Proof.Mont.AArch64.P521Field
