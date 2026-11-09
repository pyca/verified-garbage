module

-- separate module: The ordinary-field canonical/bounds transfer for the MixedMul5 machine slice (MixedMul5Field_normalized) costs 1.62s of proof versus 0.61s of imports; MixedBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulGeneric
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedMul5
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSchedule
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block

/-! Complete checked emitted field multiplication at MixedMul5Field. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def MixedMul5FieldCode : List Instr := ((mixedFnBlocks.drop 33).flatten.drop 13).take 402
def MixedMul5FieldMiddle : List Instr := ((mixedFnBlocks.drop 34).flatten.drop 19).take 316
def MixedMul5FieldFold : List Instr := ((mixedFnBlocks.drop 44).flatten.drop 15).take 28
def MixedMul5FieldTail : List Instr := ((mixedFnBlocks.drop 45).flatten.drop 11).take 20
def MixedMul5FieldFoldLoads : List Instr := loadsR .x30 pointMulFoldLowRegs 72

theorem MixedMul5Field_source : MixedMul5FieldCode=(mixedFnBlocks.flatten.drop 1069).take 402 := by
  have h := drop_flatten_prefix mixedFnBlocks 33 1056 13
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 402) h.symm

theorem MixedMul5Field_fold_hoist : hoistLoads .x30 MixedMul5FieldFold=
    some (MixedMul5FieldFoldLoads,pointMulFoldArith) := by lit_decide

theorem MixedMul5Field_split : MixedMul5FieldCode=
    MixedMul5Early++(MixedMul5FieldMiddle++(MixedMul5FieldFold++MixedMul5FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem MixedMul5Field_normalized : pointMulCanonicalZ2Code .x30 0 .x30 72 .x30 72=
    (MixedMul5Loads++pointMulRow0Z2Arithmetic)++
      (MixedMul5FieldMiddle++((MixedMul5FieldFoldLoads++pointMulFoldArith)++MixedMul5FieldTail)) := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128
    · decide
    · apply chunks_eq 128 <;> decide

theorem MixedMul5Field_run (s : State) : runBlock isa MixedMul5FieldCode s=
    runBlock isa (pointMulCanonicalZ2Code .x30 0 .x30 72 .x30 72) s := by
  rw [MixedMul5Field_split,MixedMul5Field_normalized]
  exact append_run_eq (hoistLoads_run MixedMul5_hoist)
    (append_run_eq (fun _ => rfl)
      (append_run_eq (hoistLoads_run MixedMul5Field_fold_hoist) (fun _ => rfl))) s

theorem MixedMul5Field_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x30 pa size) (hb : Ptr s .x30 pb cap) (ht : PtrW s .x30 po room)
    (hA : 72≤size) (hB : 144≤cap) (hO : 144≤room)
    (hz : s.gpr .x2=0)
    (stable : StableInput s (off pa 0) (off po 72))
    (ha' : wordsVal s.mem (off pa 0) 0 9<fieldPrime)
    (hb' : wordsVal s.mem (off pb 72) 0 9<fieldPrime) :
    WP isa (.block MixedMul5FieldCode) s fun t =>
      wordsVal t.mem (off po 72) 0 9<fieldPrime ∧
      wordsVal t.mem (off po 72) 0 9=
        (wordsVal s.mem (off pa 0) 0 9*wordsVal s.mem (off pb 72) 0 9)%fieldPrime ∧
      t.gpr .x2=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointMulStreamClob s t ∧ Outside (off po 72) 0 72 s.mem t.mem := by
  have h := point_mul_canonicalz2_ok
    (a:=0) (b:=72) (o:=72) ha hb ht hA hB hO (by decide) (by decide) (by decide)
    hz (by decide) (by decide) (by decide) stable ha' hb'
  obtain ⟨t,ht,hpost⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(MixedMul5Field_run s).trans ht,hpost⟩

end VG.Proof.Mont.AArch64.P521Field
