module

-- separate module: The inline multiply source/carry replay at MixedMul9 (MixedMul9_normalized) costs 1.27s of proof versus 0.58s of imports; MixedMul9Field composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulProduct
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

/-! Checked measured inline multiplication product at MixedMul9. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field

def MixedMul9Code : List Instr := ((mixedFnBlocks.drop 107).flatten.drop 23).take 353
def MixedMul9Early : List Instr := ((mixedFnBlocks.drop 107).flatten.drop 23).take 38
def MixedMul9Rest : List Instr := ((mixedFnBlocks.drop 108).flatten.drop 29).take 315
def MixedMul9Loads : List Instr := [
  .ldr .x .x3 .x27 72,
  .ldr .x .x4 .x27 80,
  .ldr .x .x5 .x30 216,
  .ldr .x .x6 .x30 224,
  .ldr .x .x7 .x30 232,
  .ldr .x .x8 .x30 240,
  .ldr .x .x9 .x30 248,
  .ldr .x .x10 .x30 256,
  .ldr .x .x11 .x30 264,
  .ldr .x .x12 .x30 272,
  .ldr .x .x13 .x30 280]

theorem MixedMul9_source : MixedMul9Code=(mixedFnBlocks.flatten.drop 3447).take 353 := by
  have h := drop_flatten_prefix mixedFnBlocks 107 3424 23
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 353) h.symm

theorem MixedMul9_hoist : hoistLoads .x27 MixedMul9Early=some (MixedMul9Loads,pointMulRow0Z2Arithmetic) := by lit_decide

theorem MixedMul9_split : MixedMul9Code=MixedMul9Early++MixedMul9Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem MixedMul9_normalized : pointMulProductZ2Code .x27 72 .x30 216 .x30 216=
    (MixedMul9Loads++pointMulRow0Z2Arithmetic)++MixedMul9Rest := by
  apply chunks_eq 128
  · decide
  · apply chunks_eq 128 <;> decide

theorem MixedMul9_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (ha : Ptr s .x27 pa size) (hb : Ptr s .x30 pb cap) (ht : PtrW s .x30 po room)
    (hA : 144≤size) (hB : 288≤cap) (hO : 280≤room)
    (hz : s.gpr .x2=0)
    (stable : StableInput s (off pa 72) (off po 216))
    (ha' : wordsVal s.mem (off pa 72) 0 9<2^521)
    (hb' : wordsVal s.mem (off pb 216) 0 9<2^521) :
    WP isa (.block MixedMul9Code) s
      (PointMulProductInv s (off pa 72) (off po 216) (wordsVal s.mem (off pb 216) 0 9)) := by
  have h := point_mul_product_z2_ok (a:=72) (b:=216) (o:=216) ha hb ht hA hB hO
    (by decide) (by decide) (by decide) hz (by decide) (by decide) (by decide) stable ha' hb'
  rw [MixedMul9_normalized,WP.block_append_iff] at h
  rw [MixedMul9_split,WP.block_append_iff]
  exact WP.hoistLoads MixedMul9_hoist h

end VG.Proof.Mont.AArch64.P521Field
