module

-- separate module: The inline multiply source/carry replay at MixedMul4 (MixedMul4_normalized) costs 1.28s of proof versus 0.51s of imports; MixedMul4Field composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulProduct
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

/-! Checked measured inline multiplication product at MixedMul4. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field

def MixedMul4Code : List Instr := ((mixedFnBlocks.drop 20).flatten.drop 27).take 353
def MixedMul4Early : List Instr := ((mixedFnBlocks.drop 20).flatten.drop 27).take 38
def MixedMul4Rest : List Instr := ((mixedFnBlocks.drop 22).flatten.drop 1).take 315
def MixedMul4Loads : List Instr := [
  .ldr .x .x3 .x30 0,
  .ldr .x .x4 .x30 8,
  .ldr .x .x5 .x28 0,
  .ldr .x .x6 .x28 8,
  .ldr .x .x7 .x28 16,
  .ldr .x .x8 .x28 24,
  .ldr .x .x9 .x28 32,
  .ldr .x .x10 .x28 40,
  .ldr .x .x11 .x28 48,
  .ldr .x .x12 .x28 56,
  .ldr .x .x13 .x28 64]

theorem MixedMul4_source : MixedMul4Code=(mixedFnBlocks.flatten.drop 667).take 353 := by
  have h := drop_flatten_prefix mixedFnBlocks 20 640 27
    (by rw [List.length_flatten]; decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 353) h.symm

theorem MixedMul4_hoist : hoistLoads .x30 MixedMul4Early=some (MixedMul4Loads,pointMulRow0Z2Arithmetic) := by lit_decide

theorem MixedMul4_split : MixedMul4Code=MixedMul4Early++MixedMul4Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem MixedMul4_normalized : pointMulProductZ2Code .x30 0 .x28 0 .x30 144=
    (MixedMul4Loads++pointMulRow0Z2Arithmetic)++MixedMul4Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem MixedMul4_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x30 pa size) (hb : Ptr s .x28 pb cap) (ht : PtrW s .x30 po room)
    (hA : 72≤size) (hB : 72≤cap) (hO : 208≤room)
    (hz : s.gpr .x2=0)
    (stable : StableInput s (off pa 0) (off po 144))
    (ha' : wordsVal s.mem (off pa 0) 0 9<2^521)
    (hb' : wordsVal s.mem (off pb 0) 0 9<2^521) :
    WP isa (.block MixedMul4Code) s
      (PointMulProductInv s (off pa 0) (off po 144) (wordsVal s.mem (off pb 0) 0 9)) := by
  have h := point_mul_product_z2_ok (a:=0) (b:=0) (o:=144) ha hb ht hA hB hO
    (by decide) (by decide) (by decide) hz (by decide) (by decide) (by decide) stable ha' hb'
  rw [MixedMul4_normalized,WP.block_append_iff] at h
  rw [MixedMul4_split,WP.block_append_iff]
  exact WP.hoistLoads MixedMul4_hoist h

end VG.Proof.Mont.AArch64.P521Field
