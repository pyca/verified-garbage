module

-- separate module: The inline multiply source/carry replay at MixedMul5 (MixedMul5_normalized) costs 1.31s of proof versus 0.50s of imports; MixedMul5Field composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulProduct
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

/-! Checked measured inline multiplication product at MixedMul5. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field

def MixedMul5Code : List Instr := ((mixedFnBlocks.drop 33).flatten.drop 13).take 353
def MixedMul5Early : List Instr := ((mixedFnBlocks.drop 33).flatten.drop 13).take 38
def MixedMul5Rest : List Instr := ((mixedFnBlocks.drop 34).flatten.drop 19).take 315
def MixedMul5Loads : List Instr := [
  .ldr .x .x3 .x30 0,
  .ldr .x .x4 .x30 8,
  .ldr .x .x5 .x30 72,
  .ldr .x .x6 .x30 80,
  .ldr .x .x7 .x30 88,
  .ldr .x .x8 .x30 96,
  .ldr .x .x9 .x30 104,
  .ldr .x .x10 .x30 112,
  .ldr .x .x11 .x30 120,
  .ldr .x .x12 .x30 128,
  .ldr .x .x13 .x30 136]

theorem MixedMul5_source : MixedMul5Code=(mixedFnBlocks.flatten.drop 1069).take 353 := by
  have h := drop_flatten_prefix mixedFnBlocks 33 1056 13
    (by rw [List.length_flatten]; decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 353) h.symm

theorem MixedMul5_hoist : hoistLoads .x30 MixedMul5Early=some (MixedMul5Loads,pointMulRow0Z2Arithmetic) := by lit_decide

theorem MixedMul5_split : MixedMul5Code=MixedMul5Early++MixedMul5Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem MixedMul5_normalized : pointMulProductZ2Code .x30 0 .x30 72 .x30 72=
    (MixedMul5Loads++pointMulRow0Z2Arithmetic)++MixedMul5Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem MixedMul5_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x30 pa size) (hb : Ptr s .x30 pb cap) (ht : PtrW s .x30 po room)
    (hA : 72≤size) (hB : 144≤cap) (hO : 136≤room)
    (hz : s.gpr .x2=0)
    (stable : StableInput s (off pa 0) (off po 72))
    (ha' : wordsVal s.mem (off pa 0) 0 9<2^521)
    (hb' : wordsVal s.mem (off pb 72) 0 9<2^521) :
    WP isa (.block MixedMul5Code) s
      (PointMulProductInv s (off pa 0) (off po 72) (wordsVal s.mem (off pb 72) 0 9)) := by
  have h := point_mul_product_z2_ok (a:=0) (b:=72) (o:=72) ha hb ht hA hB hO
    (by decide) (by decide) (by decide) hz (by decide) (by decide) (by decide) stable ha' hb'
  rw [MixedMul5_normalized,WP.block_append_iff] at h
  rw [MixedMul5_split,WP.block_append_iff]
  exact WP.hoistLoads MixedMul5_hoist h

end VG.Proof.Mont.AArch64.P521Field
