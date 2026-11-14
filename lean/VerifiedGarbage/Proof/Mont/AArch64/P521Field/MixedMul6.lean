module

-- separate module: The inline multiply source/carry replay at MixedMul6 (MixedMul6_normalized) costs 1.32s of proof versus 0.55s of imports; MixedMul6Field composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulProduct
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

/-! Checked measured inline multiplication product at MixedMul6. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field

def MixedMul6Code : List Instr := ((mixedFnBlocks.drop 64).flatten.drop 7).take 355
def MixedMul6Early : List Instr := ((mixedFnBlocks.drop 64).flatten.drop 7).take 39
def MixedMul6Rest : List Instr := ((mixedFnBlocks.drop 65).flatten.drop 14).take 316
def MixedMul6Loads : List Instr := [
  .ldr .x .x3 .x30 216,
  .ldr .x .x4 .x30 224,
  .ldr .x .x5 .x27 0,
  .ldr .x .x6 .x27 8,
  .ldr .x .x7 .x27 16,
  .ldr .x .x8 .x27 24,
  .ldr .x .x9 .x27 32,
  .ldr .x .x10 .x27 40,
  .ldr .x .x11 .x27 48,
  .ldr .x .x12 .x27 56,
  .ldr .x .x13 .x27 64]

theorem MixedMul6_source : MixedMul6Code=(mixedFnBlocks.flatten.drop 2055).take 355 := by
  have h := drop_flatten_prefix mixedFnBlocks 64 2048 7
    (by rw [List.length_flatten]; decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 355) h.symm

theorem MixedMul6_hoist : hoistLoads .x30 MixedMul6Early=some (MixedMul6Loads,pointMulRow0Arithmetic) := by lit_decide

theorem MixedMul6_split : MixedMul6Code=MixedMul6Early++MixedMul6Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem MixedMul6_normalized : pointMulProductCode .x30 216 .x27 0 .x30 288=
    (MixedMul6Loads++pointMulRow0Arithmetic)++MixedMul6Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem MixedMul6_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x30 pa size) (hb : Ptr s .x27 pb cap) (ht : PtrW s .x30 po room)
    (hA : 288≤size) (hB : 72≤cap) (hO : 352≤room)
    (stable : StableInput s (off pa 216) (off po 288))
    (ha' : wordsVal s.mem (off pa 216) 0 9<2^521)
    (hb' : wordsVal s.mem (off pb 0) 0 9<2^521) :
    WP isa (.block MixedMul6Code) s
      (PointMulProductInv s (off pa 216) (off po 288) (wordsVal s.mem (off pb 0) 0 9)) := by
  have h := point_mul_product_ok (a:=216) (b:=0) (o:=288) ha hb ht hA hB hO
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) stable ha' hb'
  rw [MixedMul6_normalized,WP.block_append_iff] at h
  rw [MixedMul6_split,WP.block_append_iff]
  exact WP.hoistLoads MixedMul6_hoist h

end VG.Proof.Mont.AArch64.P521Field
