module

-- separate module: The inline symmetric-square hoist/source replay at MixedSquare7 (MixedSquare7_normalized) costs 1.04s of proof versus 0.37s of imports; MixedBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSquareGenericZ1
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Block

/-! Checked measured instruction schedule for inline square site MixedSquare7. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def MixedSquare7Code : List Instr := ((mixedFnBlocks.drop 56).flatten.drop 18).take 245
def MixedSquare7Early : List Instr := ((mixedFnBlocks.drop 56).flatten.drop 18).take 29
def MixedSquare7Rest : List Instr := ((mixedFnBlocks.drop 57).flatten.drop 15).take 216
def MixedSquare7Loads : List Instr := [
  .ldr .x .x2 .x30 72,
  .ldr .x .x3 .x30 80,
  .ldr .x .x4 .x30 88,
  .ldr .x .x5 .x30 96,
  .ldr .x .x6 .x30 104,
  .ldr .x .x7 .x30 112,
  .ldr .x .x8 .x30 120,
  .ldr .x .x9 .x30 128]

theorem MixedSquare7Code_source : MixedSquare7Code=(mixedFnBlocks.flatten.drop 1810).take 245 := by
  have h := drop_flatten_prefix mixedFnBlocks 56 1792 18
    (by rw [List.length_flatten]; decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 245) h.symm

theorem MixedSquare7_hoist : hoistLoads .x30 MixedSquare7Early =
    some (MixedSquare7Loads,pointCross0Z1Code) := by decide

theorem MixedSquare7_split : MixedSquare7Code=MixedSquare7Early++MixedSquare7Rest := by
  apply chunks_eq 128 <;> decide

theorem MixedSquare7_normalized : pointSquareNormalizedZ1 .x30 72 .x30 0=
    (MixedSquare7Loads++pointCross0Z1Code)++MixedSquare7Rest := by
  apply chunks_eq 128 <;> decide

theorem MixedSquare7_ok {s : State} {p q : Addr} {size cap : Nat}
    (hp : Ptr s .x30 p size) (hq : PtrW s .x30 q cap)
    (hd : 144≤size) (ho : 72≤cap)
    (hz : s.gpr .x1=0)
    (ha : wordsVal s.mem p 72 9<fieldPrime) :
    WP isa (.block MixedSquare7Code) s fun t =>
      wordsVal t.mem q 0 9<fieldPrime ∧
      wordsVal t.mem q 0 9=(wordsVal s.mem p 72 9*wordsVal s.mem p 72 9)%fieldPrime ∧
      t.gpr .x1=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointFullProductClob s t ∧ Outside q 0 72 s.mem t.mem := by
  have h := point_square_normalized_z1_ok (d:=72) (o:=0) hp hq hd ho (by decide) (by decide) hz (by decide) (by decide) ha
  rw [MixedSquare7_normalized,WP.block_append_iff] at h
  rw [MixedSquare7_split,WP.block_append_iff]
  exact WP.hoistLoads MixedSquare7_hoist h

end VG.Proof.Mont.AArch64.P521Field
