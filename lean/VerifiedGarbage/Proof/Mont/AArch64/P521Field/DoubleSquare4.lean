module

-- separate module: The inline symmetric-square hoist/source replay at DoubleSquare4 (DoubleSquare4_normalized) costs 1.06s of proof versus 0.37s of imports; DoubleBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSquareGenericZ1
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Block

/-! Checked measured instruction schedule for inline square site DoubleSquare4. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def DoubleSquare4Code : List Instr := ((doubleFnBlocks.drop 66).flatten.drop 19).take 245
def DoubleSquare4Early : List Instr := ((doubleFnBlocks.drop 66).flatten.drop 19).take 29
def DoubleSquare4Rest : List Instr := ((doubleFnBlocks.drop 67).flatten.drop 16).take 216
def DoubleSquare4Loads : List Instr := [
  .ldr .x .x2 .x28 72,
  .ldr .x .x3 .x28 80,
  .ldr .x .x4 .x28 88,
  .ldr .x .x5 .x28 96,
  .ldr .x .x6 .x28 104,
  .ldr .x .x7 .x28 112,
  .ldr .x .x8 .x28 120,
  .ldr .x .x9 .x28 128]

theorem DoubleSquare4Code_source : DoubleSquare4Code=(doubleFnBlocks.flatten.drop 2131).take 245 := by
  have h := drop_flatten_prefix doubleFnBlocks 66 2112 19
    (by rw [List.length_flatten]; decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 245) h.symm

theorem DoubleSquare4_hoist : hoistLoads .x28 DoubleSquare4Early =
    some (DoubleSquare4Loads,pointCross0Z1Code) := by decide

theorem DoubleSquare4_split : DoubleSquare4Code=DoubleSquare4Early++DoubleSquare4Rest := by
  apply chunks_eq 128 <;> decide

theorem DoubleSquare4_normalized : pointSquareNormalizedZ1 .x28 72 .x28 288=
    (DoubleSquare4Loads++pointCross0Z1Code)++DoubleSquare4Rest := by
  apply chunks_eq 128 <;> decide

theorem DoubleSquare4_ok {s : State} {p q : Addr} {size cap : Nat}
    (hp : Ptr s .x28 p size) (hq : PtrW s .x28 q cap)
    (hd : 144≤size) (ho : 360≤cap)
    (hz : s.gpr .x1=0)
    (ha : wordsVal s.mem p 72 9<fieldPrime) :
    WP isa (.block DoubleSquare4Code) s fun t =>
      wordsVal t.mem q 288 9<fieldPrime ∧
      wordsVal t.mem q 288 9=(wordsVal s.mem p 72 9*wordsVal s.mem p 72 9)%fieldPrime ∧
      t.gpr .x1=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointFullProductClob s t ∧ Outside q 288 72 s.mem t.mem := by
  have h := point_square_normalized_z1_ok (d:=72) (o:=288) hp hq hd ho (by decide) (by decide) hz (by decide) (by decide) ha
  rw [DoubleSquare4_normalized,WP.block_append_iff] at h
  rw [DoubleSquare4_split,WP.block_append_iff]
  exact WP.hoistLoads DoubleSquare4_hoist h

end VG.Proof.Mont.AArch64.P521Field
