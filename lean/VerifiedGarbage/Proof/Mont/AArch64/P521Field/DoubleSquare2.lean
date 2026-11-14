module

-- separate module: The inline symmetric-square hoist/source replay at DoubleSquare2 (DoubleSquare2_normalized) costs 1.21s of proof versus 0.50s of imports; DoubleBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSquareGeneric
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Block

/-! Checked measured instruction schedule for inline square site DoubleSquare2. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def DoubleSquare2Code : List Instr := ((doubleFnBlocks.drop 33).flatten.drop 3).take 247
def DoubleSquare2Early : List Instr := ((doubleFnBlocks.drop 33).flatten.drop 3).take 30
def DoubleSquare2Rest : List Instr := ((doubleFnBlocks.drop 34).flatten.drop 1).take 217
def DoubleSquare2Loads : List Instr := [
  .ldr .x .x2 .x28 144,
  .ldr .x .x3 .x28 152,
  .ldr .x .x4 .x28 160,
  .ldr .x .x5 .x28 168,
  .ldr .x .x6 .x28 176,
  .ldr .x .x7 .x28 184,
  .ldr .x .x8 .x28 192,
  .ldr .x .x9 .x28 200]

theorem DoubleSquare2Code_source : DoubleSquare2Code=(doubleFnBlocks.flatten.drop 1059).take 247 := by
  have h := drop_flatten_prefix doubleFnBlocks 33 1056 3
    (by rw [List.length_flatten]; decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 247) h.symm

theorem DoubleSquare2_hoist : hoistLoads .x28 DoubleSquare2Early =
    some (DoubleSquare2Loads,pointCross0Code) := by decide

theorem DoubleSquare2_split : DoubleSquare2Code=DoubleSquare2Early++DoubleSquare2Rest := by
  apply chunks_eq 128 <;> decide

theorem DoubleSquare2_normalized : pointSquareNormalized .x28 144 .x28 432=
    (DoubleSquare2Loads++pointCross0Code)++DoubleSquare2Rest := by
  apply chunks_eq 128 <;> decide

theorem DoubleSquare2_ok {s : State} {p q : Addr} {size cap : Nat}
    (hp : Ptr s .x28 p size) (hq : PtrW s .x28 q cap)
    (hd : 216≤size) (ho : 504≤cap)
    (ha : wordsVal s.mem p 144 9<fieldPrime) :
    WP isa (.block DoubleSquare2Code) s fun t =>
      wordsVal t.mem q 432 9<fieldPrime ∧
      wordsVal t.mem q 432 9=(wordsVal s.mem p 144 9*wordsVal s.mem p 144 9)%fieldPrime ∧
      t.gpr .x1=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointFullProductClob s t ∧ Outside q 432 72 s.mem t.mem := by
  have h := point_square_normalized_ok (d:=144) (o:=432) hp hq hd ho (by decide) (by decide) (by decide) (by decide) ha
  rw [DoubleSquare2_normalized,WP.block_append_iff] at h
  rw [DoubleSquare2_split,WP.block_append_iff]
  exact WP.hoistLoads DoubleSquare2_hoist h

end VG.Proof.Mont.AArch64.P521Field
