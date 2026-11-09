module

-- separate module: The inline multiply source/carry replay at MixedMul3 (MixedMul3_normalized) costs 1.38s of proof versus 0.41s of imports; MixedMul3Field composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulProduct
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

/-! Checked measured inline multiplication product at MixedMul3. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field

def MixedMul3Code : List Instr := ((mixedFnBlocks.drop 8).flatten.drop 7).take 355
def MixedMul3Early : List Instr := ((mixedFnBlocks.drop 8).flatten.drop 7).take 39
def MixedMul3Rest : List Instr := ((mixedFnBlocks.drop 9).flatten.drop 14).take 316
def MixedMul3Loads : List Instr := [
  .ldr .x .x3 .x27 144,
  .ldr .x .x4 .x27 152,
  .ldr .x .x5 .x28 72,
  .ldr .x .x6 .x28 80,
  .ldr .x .x7 .x28 88,
  .ldr .x .x8 .x28 96,
  .ldr .x .x9 .x28 104,
  .ldr .x .x10 .x28 112,
  .ldr .x .x11 .x28 120,
  .ldr .x .x12 .x28 128,
  .ldr .x .x13 .x28 136]

theorem MixedMul3_source : MixedMul3Code=(mixedFnBlocks.flatten.drop 263).take 355 := by
  have h := drop_flatten_prefix mixedFnBlocks 8 256 7
    (by rw [List.length_flatten]; decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 355) h.symm

theorem MixedMul3_hoist : hoistLoads .x27 MixedMul3Early=some (MixedMul3Loads,pointMulRow0Arithmetic) := by lit_decide

theorem MixedMul3_split : MixedMul3Code=MixedMul3Early++MixedMul3Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem MixedMul3_normalized : pointMulProductCode .x27 144 .x28 72 .x30 72=
    (MixedMul3Loads++pointMulRow0Arithmetic)++MixedMul3Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem MixedMul3_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x27 pa size) (hb : Ptr s .x28 pb cap) (ht : PtrW s .x30 po room)
    (hA : 216≤size) (hB : 144≤cap) (hO : 136≤room)
    (stable : StableInput s (off pa 144) (off po 72))
    (ha' : wordsVal s.mem (off pa 144) 0 9<2^521)
    (hb' : wordsVal s.mem (off pb 72) 0 9<2^521) :
    WP isa (.block MixedMul3Code) s
      (PointMulProductInv s (off pa 144) (off po 72) (wordsVal s.mem (off pb 72) 0 9)) := by
  have h := point_mul_product_ok (a:=144) (b:=72) (o:=72) ha hb ht hA hB hO
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) stable ha' hb'
  rw [MixedMul3_normalized,WP.block_append_iff] at h
  rw [MixedMul3_split,WP.block_append_iff]
  exact WP.hoistLoads MixedMul3_hoist h

end VG.Proof.Mont.AArch64.P521Field
