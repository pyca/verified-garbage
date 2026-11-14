module

-- separate module: The inline symmetric-square hoist/source replay at MixedSquare6 (MixedSquare6_normalized) costs 1.14s of proof versus 0.45s of imports; MixedBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSquareGeneric
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Block

/-! Checked measured instruction schedule for inline square site MixedSquare6. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def MixedSquare6Code : List Instr := ((mixedFnBlocks.drop 48).flatten.drop 27).take 247
def MixedSquare6Early : List Instr := ((mixedFnBlocks.drop 48).flatten.drop 27).take 30
def MixedSquare6Rest : List Instr := ((mixedFnBlocks.drop 49).flatten.drop 25).take 217
def MixedSquare6Loads : List Instr := [
  .ldr .x .x2 .x30 360,
  .ldr .x .x3 .x30 368,
  .ldr .x .x4 .x30 376,
  .ldr .x .x5 .x30 384,
  .ldr .x .x6 .x30 392,
  .ldr .x .x7 .x30 400,
  .ldr .x .x8 .x30 408,
  .ldr .x .x9 .x30 416]

theorem MixedSquare6Code_source : MixedSquare6Code=(mixedFnBlocks.flatten.drop 1563).take 247 := by
  have h := drop_flatten_prefix mixedFnBlocks 48 1536 27
    (by rw [List.length_flatten]; decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 247) h.symm

theorem MixedSquare6_hoist : hoistLoads .x30 MixedSquare6Early =
    some (MixedSquare6Loads,pointCross0Code) := by lit_decide

theorem MixedSquare6_split : MixedSquare6Code=MixedSquare6Early++MixedSquare6Rest := by
  apply chunks_eq 128 <;> decide

theorem MixedSquare6_normalized : pointSquareNormalized .x30 360 .x30 216=
    (MixedSquare6Loads++pointCross0Code)++MixedSquare6Rest := by
  apply chunks_eq 128 <;> decide

theorem MixedSquare6_ok {s : State} {p q : Addr} {size cap : Nat}
    (hp : Ptr s .x30 p size) (hq : PtrW s .x30 q cap)
    (hd : 432≤size) (ho : 288≤cap)
    (ha : wordsVal s.mem p 360 9<fieldPrime) :
    WP isa (.block MixedSquare6Code) s fun t =>
      wordsVal t.mem q 216 9<fieldPrime ∧
      wordsVal t.mem q 216 9=(wordsVal s.mem p 360 9*wordsVal s.mem p 360 9)%fieldPrime ∧
      t.gpr .x1=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointFullProductClob s t ∧ Outside q 216 72 s.mem t.mem := by
  have h := point_square_normalized_ok (d:=360) (o:=216) hp hq hd ho (by decide) (by decide) (by decide) (by decide) ha
  rw [MixedSquare6_normalized,WP.block_append_iff] at h
  rw [MixedSquare6_split,WP.block_append_iff]
  exact WP.hoistLoads MixedSquare6_hoist h

end VG.Proof.Mont.AArch64.P521Field
