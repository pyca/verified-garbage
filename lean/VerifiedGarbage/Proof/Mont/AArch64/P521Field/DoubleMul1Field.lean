module

-- separate module: The ordinary-field canonical/bounds transfer for the DoubleMul1 machine slice (DoubleMul1Field_normalized) costs 1.37s of proof versus 0.53s of imports; DoubleBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulGeneric
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleMul1
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSchedule
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block

/-! Complete checked emitted field multiplication at DoubleMul1Field. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def DoubleMul1FieldCode : List Instr := ((doubleFnBlocks.drop 40).flatten.drop 26).take 392
def DoubleMul1FieldMiddle : List Instr := ((doubleFnBlocks.drop 42).flatten.drop 1).take 316
def DoubleMul1FieldFold : List Instr := ((doubleFnBlocks.drop 51).flatten.drop 29).take 28
def DoubleMul1FieldTail : List Instr := ((doubleFnBlocks.drop 52).flatten.drop 25).take 9
def DoubleMul1FieldFoldLoads : List Instr := loadsR .x28 pointMulFoldLowRegs 216

theorem DoubleMul1Field_source : DoubleMul1FieldCode=(doubleFnBlocks.flatten.drop 1306).take 392 := by
  have h := drop_flatten_prefix doubleFnBlocks 40 1280 26
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 392) h.symm

theorem DoubleMul1Field_fold_hoist : hoistLoads .x28 DoubleMul1FieldFold=
    some (DoubleMul1FieldFoldLoads,pointMulWeakArith) := by lit_decide

theorem DoubleMul1Field_split : DoubleMul1FieldCode=
    DoubleMul1Early++(DoubleMul1FieldMiddle++(DoubleMul1FieldFold++DoubleMul1FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem DoubleMul1Field_normalized : pointMulWeakCode .x27 0 .x28 72 .x28 216=
    (DoubleMul1Loads++pointMulRow0Arithmetic)++
      (DoubleMul1FieldMiddle++((DoubleMul1FieldFoldLoads++pointMulWeakArith)++DoubleMul1FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem DoubleMul1Field_run (s : State) : runBlock isa DoubleMul1FieldCode s=
    runBlock isa (pointMulWeakCode .x27 0 .x28 72 .x28 216) s := by
  rw [DoubleMul1Field_split,DoubleMul1Field_normalized]
  exact append_run_eq (hoistLoads_run DoubleMul1_hoist)
    (append_run_eq (fun _ => rfl)
      (append_run_eq (hoistLoads_run DoubleMul1Field_fold_hoist) (fun _ => rfl))) s

theorem DoubleMul1Field_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x27 pa size) (hb : Ptr s .x28 pb cap) (ht : PtrW s .x28 po room)
    (hA : 72≤size) (hB : 144≤cap) (hO : 288≤room)
    (stable : StableInput s (off pa 0) (off po 216))
    (ha' : wordsVal s.mem (off pa 0) 0 9<fieldPrime)
    (hb' : wordsVal s.mem (off pb 72) 0 9<fieldPrime) :
    WP isa (.block DoubleMul1FieldCode) s fun t =>
      wordsVal t.mem (off po 216) 0 9<2*fieldPrime ∧
      wordsVal t.mem (off po 216) 0 9%fieldPrime=
        (wordsVal s.mem (off pa 0) 0 9*wordsVal s.mem (off pb 72) 0 9)%fieldPrime ∧
      t.gpr .x2=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointMulStreamClob s t ∧ Outside (off po 216) 0 72 s.mem t.mem := by
  have h := point_mul_weak_ok
    (a:=0) (b:=72) (o:=216) ha hb ht hA hB hO (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) stable ha' hb'
  obtain ⟨t,ht,hpost⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(DoubleMul1Field_run s).trans ht,hpost⟩

end VG.Proof.Mont.AArch64.P521Field
