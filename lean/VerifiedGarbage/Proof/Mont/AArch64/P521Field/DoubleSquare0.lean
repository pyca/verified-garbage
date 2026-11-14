module

-- separate module: The inline symmetric-square hoist/source replay at DoubleSquare0 (DoubleSquare0_normalized) costs 1.17s of proof versus 0.49s of imports; DoubleBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSquareGeneric
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Block

/-! Checked measured instruction schedule for inline square site DoubleSquare0. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def DoubleSquare0Code : List Instr := ((doubleFnBlocks.drop 0).flatten.drop 14).take 247
def DoubleSquare0Early : List Instr := ((doubleFnBlocks.drop 0).flatten.drop 14).take 30
def DoubleSquare0Rest : List Instr := ((doubleFnBlocks.drop 1).flatten.drop 12).take 217
def DoubleSquare0Loads : List Instr := [
  .ldr .x .x2 .x27 144,
  .ldr .x .x3 .x27 152,
  .ldr .x .x4 .x27 160,
  .ldr .x .x5 .x27 168,
  .ldr .x .x6 .x27 176,
  .ldr .x .x7 .x27 184,
  .ldr .x .x8 .x27 192,
  .ldr .x .x9 .x27 200]

theorem DoubleSquare0Code_source : DoubleSquare0Code=(doubleFnBlocks.flatten.drop 14).take 247 := by
  have h := drop_flatten_prefix doubleFnBlocks 0 0 14
    (by rw [List.length_flatten]; decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 247) h.symm

theorem DoubleSquare0_hoist : hoistLoads .x27 DoubleSquare0Early =
    some (DoubleSquare0Loads,pointCross0Code) := by decide

theorem DoubleSquare0_split : DoubleSquare0Code=DoubleSquare0Early++DoubleSquare0Rest := by
  apply chunks_eq 128 <;> decide

theorem DoubleSquare0_normalized : pointSquareNormalized .x27 144 .x28 0=
    (DoubleSquare0Loads++pointCross0Code)++DoubleSquare0Rest := by
  apply chunks_eq 128 <;> decide

theorem DoubleSquare0_ok {s : State} {p q : Addr} {size cap : Nat}
    (hp : Ptr s .x27 p size) (hq : PtrW s .x28 q cap)
    (hd : 216≤size) (ho : 72≤cap)
    (ha : wordsVal s.mem p 144 9<fieldPrime) :
    WP isa (.block DoubleSquare0Code) s fun t =>
      wordsVal t.mem q 0 9<fieldPrime ∧
      wordsVal t.mem q 0 9=(wordsVal s.mem p 144 9*wordsVal s.mem p 144 9)%fieldPrime ∧
      t.gpr .x1=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointFullProductClob s t ∧ Outside q 0 72 s.mem t.mem := by
  have h := point_square_normalized_ok (d:=144) (o:=0) hp hq hd ho (by decide) (by decide) (by decide) (by decide) ha
  rw [DoubleSquare0_normalized,WP.block_append_iff] at h
  rw [DoubleSquare0_split,WP.block_append_iff]
  exact WP.hoistLoads DoubleSquare0_hoist h

end VG.Proof.Mont.AArch64.P521Field
