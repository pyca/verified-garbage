module

-- separate module: The inline symmetric-square hoist/source replay at MixedSquare5 (MixedSquare5_normalized) costs 1.26s of proof versus 0.50s of imports; MixedBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSquareGeneric
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Block

/-! Checked measured instruction schedule for inline square site MixedSquare5. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def MixedSquare5Code : List Instr := ((mixedFnBlocks.drop 0).flatten.drop 16).take 247
def MixedSquare5Early : List Instr := ((mixedFnBlocks.drop 0).flatten.drop 16).take 30
def MixedSquare5Rest : List Instr := ((mixedFnBlocks.drop 1).flatten.drop 14).take 217
def MixedSquare5Loads : List Instr := [
  .ldr .x .x2 .x27 144,
  .ldr .x .x3 .x27 152,
  .ldr .x .x4 .x27 160,
  .ldr .x .x5 .x27 168,
  .ldr .x .x6 .x27 176,
  .ldr .x .x7 .x27 184,
  .ldr .x .x8 .x27 192,
  .ldr .x .x9 .x27 200]

theorem MixedSquare5Code_source : MixedSquare5Code=(mixedFnBlocks.flatten.drop 16).take 247 := by
  have h := drop_flatten_prefix mixedFnBlocks 0 0 16
    (by rw [List.length_flatten]; decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 247) h.symm

theorem MixedSquare5_hoist : hoistLoads .x27 MixedSquare5Early =
    some (MixedSquare5Loads,pointCross0Code) := by decide

theorem MixedSquare5_split : MixedSquare5Code=MixedSquare5Early++MixedSquare5Rest := by
  apply chunks_eq 128 <;> decide

theorem MixedSquare5_normalized : pointSquareNormalized .x27 144 .x30 0=
    (MixedSquare5Loads++pointCross0Code)++MixedSquare5Rest := by
  apply chunks_eq 128 <;> decide

theorem MixedSquare5_ok {s : State} {p q : Addr} {size cap : Nat}
    (hp : Ptr s .x27 p size) (hq : PtrW s .x30 q cap)
    (hd : 216≤size) (ho : 72≤cap)
    (ha : wordsVal s.mem p 144 9<fieldPrime) :
    WP isa (.block MixedSquare5Code) s fun t =>
      wordsVal t.mem q 0 9<fieldPrime ∧
      wordsVal t.mem q 0 9=(wordsVal s.mem p 144 9*wordsVal s.mem p 144 9)%fieldPrime ∧
      t.gpr .x1=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointFullProductClob s t ∧ Outside q 0 72 s.mem t.mem := by
  have h := point_square_normalized_ok (d:=144) (o:=0) hp hq hd ho (by decide) (by decide) (by decide) (by decide) ha
  rw [MixedSquare5_normalized,WP.block_append_iff] at h
  rw [MixedSquare5_split,WP.block_append_iff]
  exact WP.hoistLoads MixedSquare5_hoist h

end VG.Proof.Mont.AArch64.P521Field
