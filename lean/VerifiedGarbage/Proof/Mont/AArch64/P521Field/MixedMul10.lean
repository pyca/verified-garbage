module

-- separate module: The inline multiply source/carry replay at MixedMul10 (MixedMul10_normalized) costs 1.40s of proof versus 0.55s of imports; MixedMul10Field composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulProduct
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

/-! Checked measured inline multiplication product at MixedMul10. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field

def MixedMul10Code : List Instr := ((mixedFnBlocks.drop 120).flatten.drop 9).take 353
def MixedMul10Early : List Instr := ((mixedFnBlocks.drop 120).flatten.drop 9).take 38
def MixedMul10Rest : List Instr := ((mixedFnBlocks.drop 121).flatten.drop 15).take 315
def MixedMul10Loads : List Instr := [
  .ldr .x .x3 .x30 72,
  .ldr .x .x4 .x30 80,
  .ldr .x .x5 .x30 288,
  .ldr .x .x6 .x30 296,
  .ldr .x .x7 .x30 304,
  .ldr .x .x8 .x30 312,
  .ldr .x .x9 .x30 320,
  .ldr .x .x10 .x30 328,
  .ldr .x .x11 .x30 336,
  .ldr .x .x12 .x30 344,
  .ldr .x .x13 .x30 352]

theorem MixedMul10_source : MixedMul10Code=(mixedFnBlocks.flatten.drop 3849).take 353 := by
  have h := drop_flatten_prefix mixedFnBlocks 120 3840 9
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 353) h.symm

theorem MixedMul10_hoist : hoistLoads .x30 MixedMul10Early=some (MixedMul10Loads,pointMulRow0Z2Arithmetic) := by lit_decide

theorem MixedMul10_split : MixedMul10Code=MixedMul10Early++MixedMul10Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem MixedMul10_normalized : pointMulProductZ2Code .x30 72 .x30 288 .x30 288=
    (MixedMul10Loads++pointMulRow0Z2Arithmetic)++MixedMul10Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem MixedMul10_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x30 pa size) (hb : Ptr s .x30 pb cap) (ht : PtrW s .x30 po room)
    (hA : 144≤size) (hB : 360≤cap) (hO : 352≤room)
    (hz : s.gpr .x2=0)
    (stable : StableInput s (off pa 72) (off po 288))
    (ha' : wordsVal s.mem (off pa 72) 0 9<2^521)
    (hb' : wordsVal s.mem (off pb 288) 0 9<2^521) :
    WP isa (.block MixedMul10Code) s
      (PointMulProductInv s (off pa 72) (off po 288) (wordsVal s.mem (off pb 288) 0 9)) := by
  have h := point_mul_product_z2_ok (a:=72) (b:=288) (o:=288) ha hb ht hA hB hO
    (by decide) (by decide) (by decide) hz (by decide) (by decide) (by decide) stable ha' hb'
  rw [MixedMul10_normalized,WP.block_append_iff] at h
  rw [MixedMul10_split,WP.block_append_iff]
  exact WP.hoistLoads MixedMul10_hoist h

end VG.Proof.Mont.AArch64.P521Field
