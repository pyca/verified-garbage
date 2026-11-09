module

-- separate module: The inline symmetric-square hoist/source replay at DoubleSquare1 (DoubleSquare1_normalized) costs 0.96s of proof versus 0.37s of imports; DoubleBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSquareGenericZ1
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Block

/-! Checked measured instruction schedule for inline square site DoubleSquare1. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def DoubleSquare1Code : List Instr := ((doubleFnBlocks.drop 8).flatten.drop 5).take 245
def DoubleSquare1Early : List Instr := ((doubleFnBlocks.drop 8).flatten.drop 5).take 29
def DoubleSquare1Rest : List Instr := ((doubleFnBlocks.drop 9).flatten.drop 2).take 216
def DoubleSquare1Loads : List Instr := [
  .ldr .x .x2 .x27 72,
  .ldr .x .x3 .x27 80,
  .ldr .x .x4 .x27 88,
  .ldr .x .x5 .x27 96,
  .ldr .x .x6 .x27 104,
  .ldr .x .x7 .x27 112,
  .ldr .x .x8 .x27 120,
  .ldr .x .x9 .x27 128]

theorem DoubleSquare1Code_source : DoubleSquare1Code=(doubleFnBlocks.flatten.drop 261).take 245 := by
  have h := drop_flatten_prefix doubleFnBlocks 8 256 5
    (by rw [List.length_flatten]; decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 245) h.symm

theorem DoubleSquare1_hoist : hoistLoads .x27 DoubleSquare1Early =
    some (DoubleSquare1Loads,pointCross0Z1Code) := by decide

theorem DoubleSquare1_split : DoubleSquare1Code=DoubleSquare1Early++DoubleSquare1Rest := by
  apply chunks_eq 128 <;> decide

theorem DoubleSquare1_normalized : pointSquareNormalizedZ1 .x27 72 .x28 72=
    (DoubleSquare1Loads++pointCross0Z1Code)++DoubleSquare1Rest := by
  apply chunks_eq 128 <;> decide

theorem DoubleSquare1_ok {s : State} {p q : Addr} {size cap : Nat}
    (hp : Ptr s .x27 p size) (hq : PtrW s .x28 q cap)
    (hd : 144≤size) (ho : 144≤cap)
    (hz : s.gpr .x1=0)
    (ha : wordsVal s.mem p 72 9<fieldPrime) :
    WP isa (.block DoubleSquare1Code) s fun t =>
      wordsVal t.mem q 72 9<fieldPrime ∧
      wordsVal t.mem q 72 9=(wordsVal s.mem p 72 9*wordsVal s.mem p 72 9)%fieldPrime ∧
      t.gpr .x1=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointFullProductClob s t ∧ Outside q 72 72 s.mem t.mem := by
  have h := point_square_normalized_z1_ok (d:=72) (o:=72) hp hq hd ho (by decide) (by decide) hz (by decide) (by decide) ha
  rw [DoubleSquare1_normalized,WP.block_append_iff] at h
  rw [DoubleSquare1_split,WP.block_append_iff]
  exact WP.hoistLoads DoubleSquare1_hoist h

end VG.Proof.Mont.AArch64.P521Field
