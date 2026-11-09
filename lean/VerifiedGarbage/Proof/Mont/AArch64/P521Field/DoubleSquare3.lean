module

-- separate module: The inline symmetric-square hoist/source replay at DoubleSquare3 (DoubleSquare3_normalized) costs 1.12s of proof versus 0.55s of imports; DoubleBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSquareGeneric
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Block

/-! Checked measured instruction schedule for inline square site DoubleSquare3. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def DoubleSquare3Code : List Instr := ((doubleFnBlocks.drop 53).flatten.drop 2).take 247
def DoubleSquare3Early : List Instr := ((doubleFnBlocks.drop 53).flatten.drop 2).take 30
def DoubleSquare3Rest : List Instr := ((doubleFnBlocks.drop 54).flatten.drop 0).take 217
def DoubleSquare3Loads : List Instr := [
  .ldr .x .x2 .x28 360,
  .ldr .x .x3 .x28 368,
  .ldr .x .x4 .x28 376,
  .ldr .x .x5 .x28 384,
  .ldr .x .x6 .x28 392,
  .ldr .x .x7 .x28 400,
  .ldr .x .x8 .x28 408,
  .ldr .x .x9 .x28 416]

theorem DoubleSquare3Code_source : DoubleSquare3Code=(doubleFnBlocks.flatten.drop 1698).take 247 := by
  have h := drop_flatten_prefix doubleFnBlocks 53 1696 2
    (by rw [List.length_flatten]; decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 247) h.symm

theorem DoubleSquare3_hoist : hoistLoads .x28 DoubleSquare3Early =
    some (DoubleSquare3Loads,pointCross0Code) := by lit_decide

theorem DoubleSquare3_split : DoubleSquare3Code=DoubleSquare3Early++DoubleSquare3Rest := by
  apply chunks_eq 128 <;> decide

theorem DoubleSquare3_normalized : pointSquareNormalized .x28 360 .x28 288=
    (DoubleSquare3Loads++pointCross0Code)++DoubleSquare3Rest := by
  apply chunks_eq 128 <;> decide

theorem DoubleSquare3_ok {s : State} {p q : Addr} {size cap : Nat}
    (hp : Ptr s .x28 p size) (hq : PtrW s .x28 q cap)
    (hd : 432≤size) (ho : 360≤cap)
    (ha : wordsVal s.mem p 360 9<fieldPrime) :
    WP isa (.block DoubleSquare3Code) s fun t =>
      wordsVal t.mem q 288 9<fieldPrime ∧
      wordsVal t.mem q 288 9=(wordsVal s.mem p 360 9*wordsVal s.mem p 360 9)%fieldPrime ∧
      t.gpr .x1=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointFullProductClob s t ∧ Outside q 288 72 s.mem t.mem := by
  have h := point_square_normalized_ok (d:=360) (o:=288) hp hq hd ho (by decide) (by decide) (by decide) (by decide) ha
  rw [DoubleSquare3_normalized,WP.block_append_iff] at h
  rw [DoubleSquare3_split,WP.block_append_iff]
  exact WP.hoistLoads DoubleSquare3_hoist h

end VG.Proof.Mont.AArch64.P521Field
