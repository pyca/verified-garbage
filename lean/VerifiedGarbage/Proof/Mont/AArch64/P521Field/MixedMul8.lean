module

-- separate module: The inline multiply source/carry replay at MixedMul8 (MixedMul8_normalized) costs 1.33s of proof versus 0.57s of imports; MixedMul8Field composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulProduct
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

/-! Checked measured inline multiplication product at MixedMul8. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field

def MixedMul8Code : List Instr := ((mixedFnBlocks.drop 92).flatten.drop 9).take 353
def MixedMul8Early : List Instr := ((mixedFnBlocks.drop 92).flatten.drop 9).take 38
def MixedMul8Rest : List Instr := ((mixedFnBlocks.drop 93).flatten.drop 15).take 315
def MixedMul8Loads : List Instr := [
  .ldr .x .x3 .x27 144,
  .ldr .x .x4 .x27 152,
  .ldr .x .x5 .x30 360,
  .ldr .x .x6 .x30 368,
  .ldr .x .x7 .x30 376,
  .ldr .x .x8 .x30 384,
  .ldr .x .x9 .x30 392,
  .ldr .x .x10 .x30 400,
  .ldr .x .x11 .x30 408,
  .ldr .x .x12 .x30 416,
  .ldr .x .x13 .x30 424]

theorem MixedMul8_source : MixedMul8Code=(mixedFnBlocks.flatten.drop 2953).take 353 := by
  have h := drop_flatten_prefix mixedFnBlocks 92 2944 9
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 353) h.symm

theorem MixedMul8_hoist : hoistLoads .x27 MixedMul8Early=some (MixedMul8Loads,pointMulRow0Z2Arithmetic) := by lit_decide

theorem MixedMul8_split : MixedMul8Code=MixedMul8Early++MixedMul8Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem MixedMul8_normalized : pointMulProductZ2Code .x27 144 .x30 360 .x30 360=
    (MixedMul8Loads++pointMulRow0Z2Arithmetic)++MixedMul8Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem MixedMul8_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x27 pa size) (hb : Ptr s .x30 pb cap) (ht : PtrW s .x30 po room)
    (hA : 216≤size) (hB : 432≤cap) (hO : 424≤room)
    (hz : s.gpr .x2=0)
    (stable : StableInput s (off pa 144) (off po 360))
    (ha' : wordsVal s.mem (off pa 144) 0 9<2^521)
    (hb' : wordsVal s.mem (off pb 360) 0 9<2^521) :
    WP isa (.block MixedMul8Code) s
      (PointMulProductInv s (off pa 144) (off po 360) (wordsVal s.mem (off pb 360) 0 9)) := by
  have h := point_mul_product_z2_ok (a:=144) (b:=360) (o:=360) ha hb ht hA hB hO
    (by decide) (by decide) (by decide) hz (by decide) (by decide) (by decide) stable ha' hb'
  rw [MixedMul8_normalized,WP.block_append_iff] at h
  rw [MixedMul8_split,WP.block_append_iff]
  exact WP.hoistLoads MixedMul8_hoist h

end VG.Proof.Mont.AArch64.P521Field
